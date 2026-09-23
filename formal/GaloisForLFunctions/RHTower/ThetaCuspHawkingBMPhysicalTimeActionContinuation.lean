import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhysicalModeAction
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhysicalFundamentalMoment

/-! Continuation and exact fundamental residue of the actual projected Einstein temporal current. -/
namespace RHTower.D4BMPhysicalModeAction
open Complex Set Filter Topology MeasureTheory
open GaloisForLFunctions.HTGeometry D4BMJointSource D4BMJointWave D4BMLaplaceRadial D4BMModularCore
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

private theorem mode_frequency_analytic (q : XiZeroCopy) (outer : Bool) (w : ℂ)
    (hw : w.im ≠ 0) (t : ℝ) (ht : t < 0) :
    AnalyticAt ℂ (fun v => tortoiseMode outer v (physicalRadialFrequency q) t) w := by
  cases outer
  · exact horizon_frequency_analyticAt w (physicalRadialFrequency q) hw (horizonCoordinate_interior t ht)
  · exact (normalizable_frequency_entire (physicalRadialFrequency q) (horizonCoordinate_interior t ht)).analyticAt w

private theorem projectedSource_meromorphic (q : XiZeroCopy) (branch : Bool) (u a w : ℂ)
    (hw : w.im ≠ 0) (hwr : -2 < w.re) (t : ℝ) (ht : t < 0) :
    MeromorphicAt (fun v => continuedAngularSourceProjection q branch u a v t) w := by
  simp_rw [continuedAngularSourceProjection_eq]
  exact ((reducedCoefficient_continued_meromorphic (physicalRate q branch) a t w).mul
    (show AnalyticAt ℂ (fun _ : ℂ => scalarResidualPeriod q u) w from analyticAt_const).meromorphicAt).add
      (MeromorphicAt.fun_sum (s := (Finset.univ : Finset (Fin 3))) (fun i _ =>
        (((show AnalyticAt ℂ (fun _ : ℂ => (horizonCoordinate t:ℂ)) w from analyticAt_const).meromorphicAt.mul
          (continuedPrincipalDifference_meromorphicAt q branch w a hw hwr i t ht)).mul
          (show AnalyticAt ℂ (fun _ : ℂ => scalarCutoffPeriod u (principalExponent q i)) w
            from analyticAt_const).meromorphicAt)))

/-- All four actual projected-source channels are analytic at both fundamental frequencies of the source copy. -/
theorem projectedSource_fundamental_analytic (q : XiZeroCopy) (branch side : Bool) (u a : ℂ)
    (t : ℝ) (ht : t < 0) :
    AnalyticAt ℂ (fun v => continuedAngularSourceProjection q branch u a v t)
      (physicalFundamentalFrequency q side) := by
  let w := physicalFundamentalFrequency q side
  let s := physicalRate q branch
  have ho : AnalyticAt ℂ (continuedOnset s) w :=
    (analyticAt_const.div (analyticAt_id.sub analyticAt_const)
      (physicalFundamentalFrequency_sub_sourceRate_ne_zero q branch side)).add
        ((onsetCorrection_entire (2*s)).analyticAt w)
  have hA : AnalyticAt ℂ (fun v => sourceAmplitude s v a (continuedOnset s v) t) w := by
    unfold sourceAmplitude
    fun_prop
  have hP : AnalyticAt ℂ (fun v => reducedPolynomial s v (radialUnit t)) w := by
    unfold reducedPolynomial liftSecondPolynomial amplitudeRate
    fun_prop
  simp_rw [continuedAngularSourceProjection_eq]
  exact ((hA.mul hP).mul analyticAt_const).add
    (Finset.analyticAt_fun_sum _ (fun i _ =>
      (analyticAt_const.mul (physicalFundamental_principal_analyticAt q branch side a i t ht)).mul
        analyticAt_const))

/-- The complete temporal current continues the actual Einstein current; its source contact is retained. -/
def continuedPhysicalTimeAction (q : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (outer : Bool) (t : ℝ) (z : D4BMHorizon.Point) : ℂ :=
  let R : ℂ := tortoiseRadius t
  let lam := physicalAngularParameter q^(2 : ℕ)-1/4
  let g := tortoiseMode outer w (physicalRadialFrequency q) t
  (-2*w*(lam-2)*continuedPhysicalSelfResponse q branch w a t*g/(R^(2 : ℕ)-1)-
    w*R^(2 : ℕ)*g*continuedAngularSourceProjection q branch (physicalAngularParameter q) a w t/(R^(2 : ℕ)-1)^(2 : ℕ))*
      modeAngularSquare (physicalModeAngularJet q z)

/-- On the original physical band this is exactly component zero of the actual Einstein action current. -/
theorem continuedPhysicalTimeAction_eq_actual (q : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : 0 < w.re) (hd : 3/2 < w.re) (hwi : w.im ≠ 0) (hwr : |w.re| < 2)
    (outer : Bool) (t : Iio (0:ℝ)) (z : D4BMHorizon.Point) (hz : 0 < z 1) :
    continuedPhysicalTimeAction q branch w a outer t z =
      physicalProjectedModeAction q q branch w a hw hd hwi hwr outer t z hz 0 := by
  have h := congrFun (physicalProjectedModeAction_value q q branch w a hw hd hwi hwr outer t z hz) 0
  rw [physicalCuspProfile_eq_continuedPhysicalSelfResponse q branch w a hw hd hwi hwr t t.property] at h
  exact h.symm

/-- The actual temporal current is meromorphic throughout the original nonreal fundamental strip. -/
theorem continuedPhysicalTimeAction_meromorphic (q : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : w.im ≠ 0) (hwr : -2 < w.re) (outer : Bool) (t : ℝ) (ht : t < 0)
    (z : D4BMHorizon.Point) :
    MeromorphicAt (fun v => continuedPhysicalTimeAction q branch v a outer t z) w := by
  have hg := (mode_frequency_analytic q outer w hw t ht).meromorphicAt
  have hf := continuedPhysicalSelfResponse_meromorphicAt q branch w a hw hwr t ht
  have hF := projectedSource_meromorphic q branch (physicalAngularParameter q) a w hw hwr t ht
  have hi : MeromorphicAt (fun v : ℂ => v) w := analyticAt_id.meromorphicAt
  have hc (c : ℂ) : MeromorphicAt (fun _ : ℂ => c) w := analyticAt_const.meromorphicAt
  have hmain := (((((hc (-2)).mul hi).mul (hc (physicalAngularParameter q^(2 : ℕ)-1/4-2))).mul hf).mul hg).div
    (hc ((tortoiseRadius t:ℂ)^(2 : ℕ)-1))
  have hcontact := ((hi.mul (hc ((tortoiseRadius t:ℂ)^(2 : ℕ)))).mul hg).mul hF
  have hcontactD := hcontact.div (hc (((tortoiseRadius t:ℂ)^(2 : ℕ)-1)^(2 : ℕ)))
  exact (hmain.sub hcontactD).mul (hc (modeAngularSquare (physicalModeAngularJet q z)))

/-- The derived temporal Laurent coefficient before any angular or horizon integration. -/
def physicalTimeResidue (q : XiZeroCopy) (branch side : Bool) (a : ℂ)
    (outer : Bool) (t : ℝ) (z : D4BMHorizon.Point) : ℂ :=
  -2*physicalFundamentalFrequency q side*(physicalAngularParameter q^(2 : ℕ)-1/4-2)*
    physicalSelfResidueCoefficient q branch side a t*
      tortoiseMode outer (physicalFundamentalFrequency q side) (physicalRadialFrequency q) t/
        ((tortoiseRadius t:ℂ)^(2 : ℕ)-1)*modeAngularSquare (physicalModeAngularJet q z)

/-- The retained temporal source contact is regular, so the actual current's simple residue is exactly the field-residue pairing. -/
theorem continuedPhysicalTimeAction_residue (q : XiZeroCopy) (branch side : Bool) (a : ℂ)
    (outer : Bool) (t : ℝ) (ht : t < 0) (z : D4BMHorizon.Point) :
    Tendsto (fun w => (w-physicalFundamentalFrequency q side)*
      continuedPhysicalTimeAction q branch w a outer t z)
      (𝓝[≠] physicalFundamentalFrequency q side)
      (𝓝 (physicalTimeResidue q branch side a outer t z)) := by
  let w0 := physicalFundamentalFrequency q side
  let R : ℂ := tortoiseRadius t
  have hg := ((mode_frequency_analytic q outer w0 (physicalFundamentalFrequency_strip q side).1 t ht).continuousAt.tendsto).mono_left
    (show 𝓝[≠] w0 ≤ 𝓝 w0 from nhdsWithin_le_nhds)
  have hF := ((projectedSource_fundamental_analytic q branch side (physicalAngularParameter q) a t ht).continuousAt.tendsto).mono_left
    (show 𝓝[≠] w0 ≤ 𝓝 w0 from nhdsWithin_le_nhds)
  have hf := continuedPhysicalSelfResponse_residue_tendsto q branch side a t ht
  have hi : Tendsto (fun w : ℂ => w) (𝓝[≠] w0) (𝓝 w0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hz0 : Tendsto (fun w : ℂ => w-w0) (𝓝[≠] w0) (𝓝 0) := by
    simpa only [sub_self] using hi.sub_const w0
  have hmain := (((hi.const_mul (-2)).mul_const (physicalAngularParameter q^(2 : ℕ)-1/4-2)).mul hf).mul hg
  have hcontact := ((((hi.mul_const (R^(2 : ℕ))).mul hg).mul hF).mul hz0)
  have h := ((hmain.div_const (R^(2 : ℕ)-1)).sub (hcontact.div_const ((R^(2 : ℕ)-1)^(2 : ℕ)))).mul_const
    (modeAngularSquare (physicalModeAngularJet q z))
  simp only [mul_zero,zero_div,sub_zero] at h
  apply h.congr'
  filter_upwards [] with w
  dsimp only [continuedPhysicalTimeAction]
  ring

private theorem fundamental_roots (q : XiZeroCopy) (side : Bool) :
    physicalFundamentalFrequency q side=-3/2-Complex.I*physicalRadialFrequency q ∨
      physicalFundamentalFrequency q side=-3/2+Complex.I*physicalRadialFrequency q := by
  rw [physicalFundamentalFrequency_connection_root]
  cases side <;> simp

private theorem fundamental_mode_value (q : XiZeroCopy) (side outer : Bool)
    (t : ℝ) (ht : t < 0) :
    tortoiseMode outer (physicalFundamentalFrequency q side) (physicalRadialFrequency q) t =
      power (physicalFundamentalFrequency q side/2) (horizonCoordinate t)*
        power (1/2) (1-horizonCoordinate t) := by
  cases outer
  · change horizon _ _ _ = _
    rw [horizon_eq_normalizable_fundamental _ _ (physicalFundamentalFrequency_strip q side).1
      (fundamental_roots q side) (horizonCoordinate_interior t ht)]
    exact normalizable_fundamental_value _ _ (fundamental_roots q side) _
  · exact normalizable_fundamental_value _ _ (fundamental_roots q side) _

private theorem physical_spin_factor_ne_zero (q : XiZeroCopy) :
    physicalAngularParameter q^(2 : ℕ)-1/4-2 ≠ 0 := by
  have hi : (physicalAngularParameter q).im ≠ 0 := by
    rw [physicalAngularParameter_eq]
    simpa using div_ne_zero (xi_divisor_support_im_ne_zero q.1) (by norm_num : (2:ℝ) ≠ 0)
  intro h
  have hp : (physicalAngularParameter q-3/2)*(physicalAngularParameter q+3/2)=0 := by
    linear_combination h
  rcases mul_eq_zero.mp hp with hm | hp
  · apply hi
    have he := congrArg Complex.im hm
    simpa using he
  · apply hi
    have he := congrArg Complex.im hp
    simpa using he

/-- The physical temporal residue carries the squared original fundamental mode and exactly the original source factors. -/
theorem physicalTimeResidue_fundamental_value (q : XiZeroCopy) (branch side : Bool) (a : ℂ)
    (outer : Bool) (t : ℝ) (ht : t < 0) (z : D4BMHorizon.Point) :
    physicalTimeResidue q branch side a outer t z =
      -2*physicalFundamentalFrequency q side*(physicalAngularParameter q^(2 : ℕ)-1/4-2)/
        ((tortoiseRadius t:ℂ)^(2 : ℕ)-1)*
      (power (physicalFundamentalFrequency q side/2) (horizonCoordinate t)*
        power (1/2) (1-horizonCoordinate t))^(2 : ℕ)*
      (physicalSelfSourceCoefficient q*
        fundamentalSourceMoment (physicalFundamentalFrequency q side) (physicalRate q branch) a*
        clearedOnset (physicalRate q branch) (physicalFundamentalFrequency q side)/
        physicalFundamentalDenominatorSlope q branch side)*modeAngularSquare (physicalModeAngularJet q z) := by
  rw [physicalTimeResidue,physicalSelfResidueCoefficient_fundamental_value q branch side a t ht,
    fundamental_mode_value q side outer t ht]
  ring

/-- At an interior point the physical current introduces no additional radial cancellation:
a surviving field residue and nonzero angular bilinear square give a surviving Einstein temporal residue. -/
theorem physicalTimeResidue_ne_zero (q : XiZeroCopy) (branch side : Bool) (a : ℂ)
    (outer : Bool) (t : ℝ) (ht : t < 0) (z : D4BMHorizon.Point)
    (hf : physicalSelfResidueCoefficient q branch side a t ≠ 0)
    (hJ : modeAngularSquare (physicalModeAngularJet q z) ≠ 0) :
    physicalTimeResidue q branch side a outer t z ≠ 0 := by
  have hw : physicalFundamentalFrequency q side ≠ 0 := by
    intro h
    exact (physicalFundamentalFrequency_strip q side).1 (by rw [h]; rfl)
  have hR : (tortoiseRadius t:ℂ)^(2 : ℕ)-1 ≠ 0 := by
    exact_mod_cast (show (tortoiseRadius t)^(2 : ℕ)-1 ≠ 0 by nlinarith [tortoiseRadius_exterior t ht])
  have hg : tortoiseMode outer (physicalFundamentalFrequency q side) (physicalRadialFrequency q) t ≠ 0 := by
    rw [fundamental_mode_value q side outer t ht]
    exact mul_ne_zero (power_ne_zero _ (horizonCoordinate_interior t ht).1)
      (power_ne_zero _ (sub_pos.mpr (horizonCoordinate_interior t ht).2))
  exact mul_ne_zero (div_ne_zero
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hw)
      (physical_spin_factor_ne_zero q)) hf) hg) hR) hJ

/-- Subtracting the derived temporal residue leaves an analytic germ of the actual continued current. -/
theorem continuedPhysicalTimeAction_laurent (q : XiZeroCopy) (branch side : Bool) (a : ℂ)
    (outer : Bool) (t : ℝ) (ht : t < 0) (z : D4BMHorizon.Point) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g (physicalFundamentalFrequency q side) ∧
      (fun w => continuedPhysicalTimeAction q branch w a outer t z) =ᶠ[𝓝[≠] physicalFundamentalFrequency q side]
        (fun w => physicalTimeResidue q branch side a outer t z/(w-physicalFundamentalFrequency q side)+g w) := by
  let f := fun w => continuedPhysicalTimeAction q branch w a outer t z
  let w0 := physicalFundamentalFrequency q side
  let R := physicalTimeResidue q branch side a outer t z
  let F := Function.update (fun w => (w-w0)*f w) w0 R
  have hm : MeromorphicAt f w0 := continuedPhysicalTimeAction_meromorphic q branch w0 a
    (physicalFundamentalFrequency_strip q side).1 (abs_lt.mp (physicalFundamentalFrequency_strip q side).2).1
    outer t ht z
  have hR := continuedPhysicalTimeAction_residue q branch side a outer t ht z
  have hM : MeromorphicAt F w0 :=
    ((show AnalyticAt ℂ (fun w : ℂ => w-w0) w0 by fun_prop).meromorphicAt.mul hm).update w0 R
  have hF : AnalyticAt ℂ F w0 := hM.analyticAt (continuousAt_update_same.mpr hR)
  have hg : AnalyticAt ℂ (dslope F w0) w0 := by
    obtain ⟨p,hp⟩ := hF
    exact ⟨p.fslope,hp.has_fpower_series_dslope_fslope⟩
  refine ⟨dslope F w0,hg,?_⟩
  filter_upwards [self_mem_nhdsWithin] with w hw
  have hne : w ≠ w0 := hw
  rw [dslope_of_ne F hne,slope_def_field]
  simp only [F,Function.update_of_ne hne,Function.update_self]
  change f w = R/(w-w0)+((w-w0)*f w-R)/(w-w0)
  field_simp [sub_ne_zero.mpr hne]
  ring

end
end RHTower.D4BMPhysicalModeAction
