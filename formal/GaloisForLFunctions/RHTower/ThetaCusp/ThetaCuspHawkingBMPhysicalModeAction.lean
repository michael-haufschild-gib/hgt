import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMModeActionReconstruction
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMPhysicalCausalGreenBand
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMPhysicalResponseGreenTransport

/-! Actual projected-response and left-mode fields in the original mixed Einstein current. -/
namespace RHTower.D4BMPhysicalModeAction
open Complex Set Filter Topology MeasureTheory
open scoped ContDiff
open GaloisForLFunctions.HTGeometry ScalarTwoJet
open D4BMMixedActionCurrent D4BMJointWave D4BMJointSource D4BMLaplaceRadial
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

private theorem C2_of_second (f df G : ℝ → ℂ)
    (h : ∀ t : ℝ, t < 0 → HasDerivAt f (df t) t ∧ HasDerivAt df (G t) t)
    (hG : ContinuousOn G (Iio (0:ℝ))) : ContDiffOn ℝ 2 f (Iio (0:ℝ)) := by
  have hd : ContDiffOn ℝ 1 df (Iio (0:ℝ)) := by
    rw [show (1 : ℕ∞ω)=0+1 by rfl,contDiffOn_succ_iff_deriv_of_isOpen isOpen_Iio]
    refine ⟨fun t ht => (h t ht).2.differentiableAt.differentiableWithinAt,by simp,?_⟩
    apply contDiffOn_zero.mpr
    exact hG.congr (fun t ht => (h t ht).2.deriv)
  rw [show (2 : ℕ∞ω)=1+1 by rfl,contDiffOn_succ_iff_deriv_of_isOpen isOpen_Iio]
  refine ⟨fun t ht => (h t ht).1.differentiableAt.differentiableWithinAt,by simp,?_⟩
  exact hd.congr (fun t ht => (h t ht).1.deriv)

private theorem physicalProfile_C2 (q r : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : 0 < w.re) (hd : 3/2 < w.re) (hwi : w.im ≠ 0) (hwr : |w.re| < 2) :
    ContDiffOn ℝ 2 (physicalCuspProfile q r branch w a hw hd hwi hwr) (Iio (0:ℝ)) :=
  C2_of_second _ _ _ (physicalCuspProfile_hasDerivAt q r branch w a hw hd hwi hwr)
    (physicalCuspSecond_continuousOn q r branch w a hw hd hwi hwr)

private theorem physicalMode_C2 (r : XiZeroCopy) (w : ℂ) (hw : 1/2 < w.re) (outer : Bool) :
    ContDiffOn ℝ 2 (tortoiseMode outer w (physicalRadialFrequency r)) (Iio (0:ℝ)) := by
  have h := physicalTortoiseMode_hasDerivAt r w hw outer
  apply C2_of_second _ _ _ h
  have hg : ContinuousOn (tortoiseMode outer w (physicalRadialFrequency r)) (Iio (0:ℝ)) :=
    fun t ht => (h t ht).1.continuousAt.continuousWithinAt
  exact (continuousOn_const.sub (continuousOn_const.mul
    (angularWeight_smooth.continuous.continuousOn.pow 2))).mul hg

private theorem physicalMode_second (r : XiZeroCopy) (w : ℂ) (hw : 1/2 < w.re)
    (outer : Bool) (t : ℝ) (ht : t < 0) :
    deriv (deriv (tortoiseMode outer w (physicalRadialFrequency r))) t =
      (w^(2 : ℕ)-(physicalAngularParameter r^(2 : ℕ)-1/4)*angularWeight t^(2 : ℕ))*
        tortoiseMode outer w (physicalRadialFrequency r) t := by
  have he : deriv (tortoiseMode outer w (physicalRadialFrequency r)) =ᶠ[𝓝 t]
      tortoiseModeFirst outer w (physicalRadialFrequency r) := by
    filter_upwards [isOpen_Iio.mem_nhds ht] with x hx
    exact (physicalTortoiseMode_hasDerivAt r w hw outer x hx).1.deriv
  exact he.deriv_eq.trans (physicalTortoiseMode_hasDerivAt r w hw outer t ht).2.deriv

/-- The original exterior point at time zero and the original tortoise radius. -/
def modePoint (t : Iio (0:ℝ)) (z : D4BMHorizon.Point) (hz : 0 < z 1) :
    D4BMBackground.ExteriorPoint :=
  ⟨![0,tortoiseRadius t,z 0,z 1],tortoiseRadius_exterior t t.property,hz⟩

private theorem modePoint_angular (t : Iio (0:ℝ)) (z : D4BMHorizon.Point) (hz : 0 < z 1) :
    D4BMMetricReconstruction.angularPoint (modePoint t z hz).val=z := by
  ext i
  fin_cases i <;> rfl

/-- The actual coexact Eisenstein covector at the unchanged physical angular parameter. -/
def physicalModeAngularJet (r : XiZeroCopy) (z : D4BMHorizon.Point) (j : Fin 2) :
    ScalarTwoJet (Fin 2) ℂ := ofField (D4BMLiteralCusp.vector (physicalAngularParameter r) j) z

/-- No angular eigen-equation is supplied: it follows from the literal coexact source. -/
theorem physicalModeAngularJet_operator (r : XiZeroCopy) (z : D4BMHorizon.Point)
    (hz : 0 < z 1) (j : Fin 2) :
    angularJetOperator (z 1) (physicalModeAngularJet r z) j =
      (physicalAngularParameter r^(2 : ℕ)-1/4)*(physicalModeAngularJet r z j).value := by
  have h := D4BMLiteralCusp.vector_equation (physicalAngularParameter r) z hz j
  have he : angularJetOperator (z 1) (physicalModeAngularJet r z) j-
      (physicalModeAngularJet r z j).value =
      D4BMHorizon.roughLaplacian (D4BMLiteralCusp.vector (physicalAngularParameter r)) j z := by
    rw [D4BMHorizon.roughLaplacian_eq _ z hz
      (D4BMLiteralCusp.vector_contDiffAt (physicalAngularParameter r) 2 z hz)]
    fin_cases j <;> rfl
  rw [← he] at h
  change angularJetOperator (z 1) (physicalModeAngularJet r z) j-
      (physicalModeAngularJet r z j).value =
      -(1/4-physicalAngularParameter r^(2 : ℕ)+1)*(physicalModeAngularJet r z j).value at h
  linear_combination h

/-- Separated stream field reconstructed from the actual complete physical projection. -/
def physicalProjectedStream (q r : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : 0 < w.re) (hd : 3/2 < w.re) (hwi : w.im ≠ 0) (hwr : |w.re| < 2)
    (j : Fin 2) (x : Fin 4 → ℝ) : ℂ :=
  Complex.exp (w*(x 0:ℂ))*radiusLift (physicalCuspProfile q r branch w a hw hd hwi hwr) (x 1)*
    D4BMLiteralCusp.vector (physicalAngularParameter r) j (D4BMMetricReconstruction.angularPoint x)

/-- Opposite-time-frequency stream field built from either original homogeneous radial mode. -/
def physicalLeftModeStream (r : XiZeroCopy) (w : ℂ) (outer : Bool) (j : Fin 2) (x : Fin 4 → ℝ) : ℂ :=
  Complex.exp ((-w)*(x 0:ℂ))*radiusLift (tortoiseMode outer w (physicalRadialFrequency r)) (x 1)*
    D4BMLiteralCusp.vector (physicalAngularParameter r) j (D4BMMetricReconstruction.angularPoint x)

/-- Every slot of the reconstructed projected stream is an actual coordinate derivative. -/
theorem physicalProjectedStream_jet (q r : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : 0 < w.re) (hd : 3/2 < w.re) (hwi : w.im ≠ 0) (hwr : |w.re| < 2)
    (t : Iio (0:ℝ)) (z : D4BMHorizon.Point) (hz : 0 < z 1) (j : Fin 2) :
    ofField (physicalProjectedStream q r branch w a hw hd hwi hwr j) (modePoint t z hz).val =
      radialStreamJet (tortoiseRadius t) w (physicalCuspProfile q r branch w a hw hd hwi hwr t)
        (deriv (physicalCuspProfile q r branch w a hw hd hwi hwr) t)
        (physicalCuspSecond q r branch w a hw hd hwi hwr t) (physicalModeAngularJet r z j) := by
  have hf := (physicalProfile_C2 q r branch w a hw hd hwi hwr).contDiffAt
    (isOpen_Iio.mem_nhds t.property)
  have h := radialStreamJet_actual w (physicalCuspProfile q r branch w a hw hd hwi hwr)
    (D4BMLiteralCusp.vector (physicalAngularParameter r) j) (modePoint t z hz).val rfl
    (tortoiseRadius_exterior t t.property)
  have htor : D4BMIngoingCoordinates.tortoise ((modePoint t z hz).val 1)=t :=
    tortoise_original_inverse t t.property
  have hscalar := D4BMLiteralCusp.vector_contDiffAt (physicalAngularParameter r) 2 z hz j
  rw [htor,modePoint_angular] at h
  have hh := h hf hscalar
  rw [(physicalCuspProfile_hasDerivAt q r branch w a hw hd hwi hwr t t.property).2.deriv] at hh
  exact hh

/-- The original left-mode stream has the full actual two-jet, including its opposite time frequency. -/
theorem physicalLeftModeStream_jet (r : XiZeroCopy) (w : ℂ) (hw : 1/2 < w.re) (outer : Bool)
    (t : Iio (0:ℝ)) (z : D4BMHorizon.Point) (hz : 0 < z 1) (j : Fin 2) :
    ofField (physicalLeftModeStream r w outer j) (modePoint t z hz).val =
      radialStreamJet (tortoiseRadius t) (-w) (tortoiseMode outer w (physicalRadialFrequency r) t)
        (tortoiseModeFirst outer w (physicalRadialFrequency r) t)
        ((w^(2 : ℕ)-(physicalAngularParameter r^(2 : ℕ)-1/4)*angularWeight t^(2 : ℕ))*
          tortoiseMode outer w (physicalRadialFrequency r) t) (physicalModeAngularJet r z j) := by
  have hf := (physicalMode_C2 r w hw outer).contDiffAt (isOpen_Iio.mem_nhds t.property)
  have h := radialStreamJet_actual (-w) (tortoiseMode outer w (physicalRadialFrequency r))
    (D4BMLiteralCusp.vector (physicalAngularParameter r) j) (modePoint t z hz).val rfl
    (tortoiseRadius_exterior t t.property)
  have htor : D4BMIngoingCoordinates.tortoise ((modePoint t z hz).val 1)=t :=
    tortoise_original_inverse t t.property
  rw [htor,modePoint_angular] at h
  have hh := h hf (D4BMLiteralCusp.vector_contDiffAt (physicalAngularParameter r) 2 z hz j)
  rw [physicalMode_second r w hw outer t t.property,
    (physicalTortoiseMode_hasDerivAt r w hw outer t t.property).1.deriv] at hh
  exact hh

private theorem physicalSecond_original_radius (q r : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : 0 < w.re) (hd : 3/2 < w.re) (hwi : w.im ≠ 0) (hwr : |w.re| < 2)
    (t : Iio (0:ℝ)) :
    physicalCuspSecond q r branch w a hw hd hwi hwr t =
      (w^(2 : ℕ)-(physicalAngularParameter r^(2 : ℕ)-1/4)*
        ((tortoiseRadius t:ℂ)^(2 : ℕ)-1)/(tortoiseRadius t:ℂ)^(2 : ℕ))*
          physicalCuspProfile q r branch w a hw hd hwi hwr t-
            continuedAngularSourceProjection q branch (physicalAngularParameter r) a w t := by
  rw [physicalCuspSecond,angularWeight_original_coefficient t t.property]
  ring

/-- The literal Einstein current, evaluated on actual projected-response and left-mode fields. -/
def physicalProjectedModeAction (q r : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : 0 < w.re) (hd : 3/2 < w.re) (hwi : w.im ≠ 0) (hwr : |w.re| < 2)
    (outer : Bool) (t : Iio (0:ℝ)) (z : D4BMHorizon.Point) (hz : 0 < z 1) : Fin 4 → ℂ :=
  let p := modePoint t z hz
  fun j => (tortoiseRadius t:ℂ)^(2 : ℕ)/(z 1:ℂ)^(2 : ℕ)*
    actionSymplectic (D4BMBackground.jet (tortoiseRadius t) (z 1))
      (streamMetricJet (tortoiseRadius t)
        (fun k => ofField (physicalProjectedStream q r branch w a hw hd hwi hwr k) p.val))
      (streamMetricJet (tortoiseRadius t)
        (fun k => ofField (physicalLeftModeStream r w outer k) p.val)) j

/-- Actual current of the original physical projection, with every source contact retained. -/
theorem physicalProjectedModeAction_value (q r : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : 0 < w.re) (hd : 3/2 < w.re) (hwi : w.im ≠ 0) (hwr : |w.re| < 2)
    (outer : Bool) (t : Iio (0:ℝ)) (z : D4BMHorizon.Point) (hz : 0 < z 1) :
    let R : ℂ := tortoiseRadius t
    let lam := physicalAngularParameter r^(2 : ℕ)-1/4
    let f := physicalCuspProfile q r branch w a hw hd hwi hwr t
    let g := tortoiseMode outer w (physicalRadialFrequency r) t
    let dg := tortoiseModeFirst outer w (physicalRadialFrequency r) t
    let F := continuedAngularSourceProjection q branch (physicalAngularParameter r) a w t
    let N := modeAngularSquare (physicalModeAngularJet r z)
    physicalProjectedModeAction q r branch w a hw hd hwi hwr outer t z hz =
      ![(-2*w*(lam-2)*f*g/(R^(2 : ℕ)-1)-w*R^(2 : ℕ)*g*F/(R^(2 : ℕ)-1)^(2 : ℕ))*N,
        (-(lam-2)*physicalCuspModeCurrent q r branch w a hw hd hwi hwr outer t-
          (R*g+R^(2 : ℕ)*dg/(R^(2 : ℕ)-1))*F)*N,0,0] := by
  have hmode : 1/2 < w.re := by linarith
  unfold physicalProjectedModeAction
  simp_rw [physicalProjectedStream_jet,physicalLeftModeStream_jet r w hmode,
    physicalSecond_original_radius,angularWeight_original_coefficient t t.property,
    ← mul_div_assoc]
  have h := radial_mode_action (modePoint t z hz) w (physicalAngularParameter r^(2 : ℕ)-1/4)
    (physicalCuspProfile q r branch w a hw hd hwi hwr t)
    (deriv (physicalCuspProfile q r branch w a hw hd hwi hwr) t)
    (tortoiseMode outer w (physicalRadialFrequency r) t)
    (tortoiseModeFirst outer w (physicalRadialFrequency r) t)
    (continuedAngularSourceProjection q branch (physicalAngularParameter r) a w t)
    (physicalModeAngularJet r z)
  exact h

/-- The actual projected stream's master is precisely its complete source with the original radius weight. -/
theorem physicalProjectedStream_master (q r : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : 0 < w.re) (hd : 3/2 < w.re) (hwi : w.im ≠ 0) (hwr : |w.re| < 2)
    (t : Iio (0:ℝ)) (z : D4BMHorizon.Point) (hz : 0 < z 1) (j : Fin 2) :
    streamMasterValue (tortoiseRadius t) (z 1)
      (fun k => ofField (physicalProjectedStream q r branch w a hw hd hwi hwr k)
        (modePoint t z hz).val) j =
      -(tortoiseRadius t:ℂ)^(3 : ℕ)/((tortoiseRadius t:ℂ)^(2 : ℕ)-1)*
        continuedAngularSourceProjection q branch (physicalAngularParameter r) a w t*
        (physicalModeAngularJet r z j).value := by
  have hr : (tortoiseRadius t:ℂ) ≠ 0 := by
    exact_mod_cast (show tortoiseRadius t ≠ 0 by linarith [tortoiseRadius_exterior t t.property])
  have hR : (tortoiseRadius t:ℂ)^(2 : ℕ)-1 ≠ 0 := by
    exact_mod_cast (show (tortoiseRadius t)^(2 : ℕ)-1 ≠ 0 by nlinarith [tortoiseRadius_exterior t t.property])
  simp_rw [physicalProjectedStream_jet,physicalSecond_original_radius]
  have h := radial_stream_master (tortoiseRadius t) (z 1) w (physicalAngularParameter r^(2 : ℕ)-1/4)
    (physicalCuspProfile q r branch w a hw hd hwi hwr t)
    (deriv (physicalCuspProfile q r branch w a hw hd hwi hwr) t)
    (continuedAngularSourceProjection q branch (physicalAngularParameter r) a w t)
    hr hR (physicalModeAngularJet r z) j
  rw [physicalModeAngularJet_operator r z hz j,sub_self,mul_zero,zero_sub] at h
  simpa only [neg_div,neg_mul] using h

/-- The left mode solves the original homogeneous stream master, as a consequence of both actual equations. -/
theorem physicalLeftModeStream_master (r : XiZeroCopy) (w : ℂ) (hw : 1/2 < w.re) (outer : Bool)
    (t : Iio (0:ℝ)) (z : D4BMHorizon.Point) (hz : 0 < z 1) (j : Fin 2) :
    streamMasterValue (tortoiseRadius t) (z 1)
      (fun k => ofField (physicalLeftModeStream r w outer k) (modePoint t z hz).val) j = 0 := by
  have hr : (tortoiseRadius t:ℂ) ≠ 0 := by
    exact_mod_cast (show tortoiseRadius t ≠ 0 by linarith [tortoiseRadius_exterior t t.property])
  have hR : (tortoiseRadius t:ℂ)^(2 : ℕ)-1 ≠ 0 := by
    exact_mod_cast (show (tortoiseRadius t)^(2 : ℕ)-1 ≠ 0 by nlinarith [tortoiseRadius_exterior t t.property])
  simp_rw [physicalLeftModeStream_jet r w hw,
    angularWeight_original_coefficient t t.property,← mul_div_assoc]
  have h := radial_stream_master (tortoiseRadius t) (z 1) (-w) (physicalAngularParameter r^(2 : ℕ)-1/4)
    (tortoiseMode outer w (physicalRadialFrequency r) t)
    (tortoiseModeFirst outer w (physicalRadialFrequency r) t) 0 hr hR (physicalModeAngularJet r z) j
  rw [physicalModeAngularJet_operator r z hz j,sub_self,mul_zero,mul_zero,zero_mul,sub_zero] at h
  simpa only [neg_sq,mul_zero,sub_zero] using h


/-- The reconstructed stream is the radius lift of the actual causal transform's physical projection. -/
theorem physicalProjectedStream_causal_origin (q r : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : 0 < w.re) (hd : 3/2 < w.re) (hwi : w.im ≠ 0) (hwr : |w.re| < 2)
    (hB : D4BMNativeCircle.principalKernelGrowth q < w.re)
    (z : D4BMHorizon.Point) (j : Fin 2) :
    (fun t : ℝ => physicalProjectedStream q r branch w a hw hd hwi hwr j
      ![0,tortoiseRadius t,z 0,z 1]) =ᵐ[radialMeasure]
      (fun t : ℝ => (tortoiseRadius t:ℂ)*
        D4BMNativeLaplace.causalPhysicalProjection q r branch a w hB hwi hwr t*
        D4BMLiteralCusp.vector (physicalAngularParameter r) j z) := by
  have ha : physicalCuspProfile q r branch w a hw hd hwi hwr =ᵐ[radialMeasure]
      D4BMNativeLaplace.causalPhysicalProjection q r branch a w hB hwi hwr := by
    rw [D4BMNativeLaplace.causalPhysicalProjection_eq_response]
    exact physicalCuspProfile_ae q r branch w a hw hd hwi hwr
  filter_upwards [ha,ae_restrict_mem measurableSet_Iio] with t hp ht
  have hz : D4BMMetricReconstruction.angularPoint ![0,tortoiseRadius t,z 0,z 1]=z := by
    ext i
    fin_cases i <;> rfl
  change Complex.exp (w*(0:ℂ))*((tortoiseRadius t:ℂ)*
    physicalCuspProfile q r branch w a hw hd hwi hwr
      (D4BMIngoingCoordinates.tortoise (tortoiseRadius t)))*
    D4BMLiteralCusp.vector (physicalAngularParameter r) j
      (D4BMMetricReconstruction.angularPoint ![0,tortoiseRadius t,z 0,z 1]) = _
  rw [hz,tortoise_original_inverse t ht,hp,mul_zero,Complex.exp_zero,one_mul]

/-- The radial source contact fixed by the original Einstein current, before taking endpoints. -/
def physicalModeSourceContact (q r : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (outer : Bool) (t : ℝ) : ℂ :=
  ((tortoiseRadius t:ℂ)*tortoiseMode outer w (physicalRadialFrequency r) t+
    (tortoiseRadius t:ℂ)^(2 : ℕ)*tortoiseModeFirst outer w (physicalRadialFrequency r) t/
      ((tortoiseRadius t:ℂ)^(2 : ℕ)-1))*
    continuedAngularSourceProjection q branch (physicalAngularParameter r) a w t

/-- The actual finite-interval Einstein flux equals the full mode/source integral and both fixed endpoint contacts. -/
theorem physicalProjectedModeAction_transport (q r : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : 0 < w.re) (hd : 3/2 < w.re) (hwi : w.im ≠ 0) (hwr : |w.re| < 2)
    (outer : Bool) (s t : Iio (0:ℝ)) (hst : (s:ℝ) ≤ t)
    (z : D4BMHorizon.Point) (hz : 0 < z 1) :
    physicalProjectedModeAction q r branch w a hw hd hwi hwr outer t z hz 1-
      physicalProjectedModeAction q r branch w a hw hd hwi hwr outer s z hz 1 =
      (-(physicalAngularParameter r^(2 : ℕ)-1/4-2)*
        (∫ x in (s:ℝ)..(t:ℝ), tortoiseMode outer w (physicalRadialFrequency r) x*
          continuedAngularSourceProjection q branch (physicalAngularParameter r) a w x)-
        (physicalModeSourceContact q r branch w a outer t-
          physicalModeSourceContact q r branch w a outer s))*
        modeAngularSquare (physicalModeAngularJet r z) := by
  have hv (x : Iio (0:ℝ)) :
      physicalProjectedModeAction q r branch w a hw hd hwi hwr outer x z hz 1 =
        (-(physicalAngularParameter r^(2 : ℕ)-1/4-2)*
          physicalCuspModeCurrent q r branch w a hw hd hwi hwr outer x-
            physicalModeSourceContact q r branch w a outer x)*
          modeAngularSquare (physicalModeAngularJet r z) :=
    congrFun (physicalProjectedModeAction_value q r branch w a hw hd hwi hwr outer x z hz) 1
  rw [hv t,hv s,physicalCuspModeCurrent_integral q r branch w a hw hd hwi hwr outer
    s t hst t.property]
  ring


end
end RHTower.D4BMPhysicalModeAction
