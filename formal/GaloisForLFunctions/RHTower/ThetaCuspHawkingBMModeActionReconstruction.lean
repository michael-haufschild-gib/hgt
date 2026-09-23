import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMMixedRadialActionCurrent
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMScalarLinearEinsteinEquation
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointCoordinate

/-! Original-radius reconstruction and the actual projected mixed Einstein current. -/
namespace RHTower.D4BMPhysicalModeAction
open Complex Set Filter Topology
open GaloisForLFunctions.HTGeometry D4BMMixedActionCurrent D4BMJointWave
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

def radiusLift (f : ℝ → ℂ) (r : ℝ) : ℂ :=
  (r:ℂ)*f (D4BMIngoingCoordinates.tortoise r)
def radiusLiftFirst (f df : ℝ → ℂ) (r : ℝ) : ℂ :=
  f (D4BMIngoingCoordinates.tortoise r)+
    (r:ℂ)*df (D4BMIngoingCoordinates.tortoise r)/((r:ℂ)^(2 : ℕ)-1)
def radiusLiftSecond (df ddf : ℝ → ℂ) (r : ℝ) : ℂ :=
  ((r:ℂ)*ddf (D4BMIngoingCoordinates.tortoise r)-
    2*df (D4BMIngoingCoordinates.tortoise r))/((r:ℂ)^(2 : ℕ)-1)^(2 : ℕ)

/-- The stream's radius factor is differentiated, together with the original tortoise map. -/
theorem radiusLift_derivatives (f df ddf : ℝ → ℂ) (r : ℝ) (hr : 1 < r)
    (hf : HasDerivAt f (df (D4BMIngoingCoordinates.tortoise r))
      (D4BMIngoingCoordinates.tortoise r))
    (hd : HasDerivAt df (ddf (D4BMIngoingCoordinates.tortoise r))
      (D4BMIngoingCoordinates.tortoise r)) :
    HasDerivAt (radiusLift f) (radiusLiftFirst f df r) r ∧
    HasDerivAt (radiusLiftFirst f df) (radiusLiftSecond df ddf r) r := by
  have ht := D4BMIngoingCoordinates.tortoise_hasDerivAt r hr
  have hF := hf.scomp r ht
  have hD := hd.scomp r ht
  have hR := (hasDerivAt_id r).ofReal_comp
  have hn : (r:ℂ)^(2 : ℕ)-1 ≠ 0 := by
    exact_mod_cast (show r^(2 : ℕ)-1 ≠ 0 by nlinarith)
  constructor
  · apply (hR.mul hF).congr_deriv
    dsimp [radiusLiftFirst]
    push_cast
    ring
  · apply (hF.add ((hR.mul hD).div ((hR.pow 2).sub_const 1) hn)).congr_deriv
    dsimp [radiusLiftSecond]
    push_cast
    field_simp
    ring

/-- Full separated stream two-jet; all angular first and second slots are retained. -/
def staticStreamJet (w c cr crr : ℂ) (J : ScalarTwoJet (Fin 2) ℂ) :
    ScalarTwoJet (Fin 4) ℂ where
  value := c*J.value
  first := ![w*c*J.value,cr*J.value,c*J.first 0,c*J.first 1]
  second := ![![w^(2 : ℕ)*c*J.value,w*cr*J.value,w*c*J.first 0,w*c*J.first 1],
    ![w*cr*J.value,crr*J.value,cr*J.first 0,cr*J.first 1],
    ![w*c*J.first 0,cr*J.first 0,c*J.second 0 0,c*J.second 0 1],
    ![w*c*J.first 1,cr*J.first 1,c*J.second 1 0,c*J.second 1 1]]

def radialStreamJet (r w f df ddf : ℂ) (J : ScalarTwoJet (Fin 2) ℂ) :
    ScalarTwoJet (Fin 4) ℂ :=
  staticStreamJet w (r*f) (f+r*df/(r^(2 : ℕ)-1)) ((r*ddf-2*df)/(r^(2 : ℕ)-1)^(2 : ℕ)) J

def modeAngularSquare (J : Fin 2 → ScalarTwoJet (Fin 2) ℂ) : ℂ :=
  ∑ j : Fin 2, (J j).value^(2 : ℕ)

private def orbit (r w c cr crr : ℂ) : ℂ :=
  r^(2 : ℕ)*(r^(2 : ℕ)-1)*crr+2*r*cr-r^(2 : ℕ)/(r^(2 : ℕ)-1)*w^(2 : ℕ)*c

private theorem stream_orbit (r y w c cr crr : ℂ)
    (J : Fin 2 → ScalarTwoJet (Fin 2) ℂ) (i : Fin 2) :
    streamAngularAction y (fun j => staticStreamJet w c cr crr (J j)) i-
      streamMasterValue r y (fun j => staticStreamJet w c cr crr (J j)) i =
    -orbit r w c cr crr*(J i).value := by
  change streamAngularAction y _ i-
    (r^(2 : ℕ)*(r^(2 : ℕ)-1)*(crr*(J i).value)+2*r*(cr*(J i).value)-
      r^(2 : ℕ)/(r^(2 : ℕ)-1)*(w^(2 : ℕ)*c*(J i).value)+streamAngularAction y _ i) = _
  unfold orbit
  ring

private theorem static_action (p : D4BMBackground.ExteriorPoint)
    (w c cr crr d dr drr : ℂ) (J : Fin 2 → ScalarTwoJet (Fin 2) ℂ) :
    let r : ℂ := p.val 1
    let P := fun j => staticStreamJet w c cr crr (J j)
    let Q := fun j => staticStreamJet (-w) d dr drr (J j)
    (fun j => r^(2 : ℕ)/(p.val 3:ℂ)^(2 : ℕ)*actionSymplectic
      (D4BMBackground.jet r (p.val 3)) (streamMetricJet r P) (streamMetricJet r Q) j) =
    ![(w/(r^(2 : ℕ)*(r^(2 : ℕ)-1))*(c*orbit r w d dr drr+d*orbit r w c cr crr))*modeAngularSquare J,
      ((r^(2 : ℕ)-1)/r^(2 : ℕ)*(dr*orbit r w c cr crr-cr*orbit r w d dr drr))*modeAngularSquare J,0,0] := by
  have hr : (p.val 1:ℂ) ≠ 0 := by exact_mod_cast (show p.val 1 ≠ 0 by linarith [p.property.1])
  have hR : (p.val 1:ℂ)^(2 : ℕ)-1 ≠ 0 := by
    exact_mod_cast (show (p.val 1)^(2 : ℕ)-1 ≠ 0 by nlinarith [p.property.1])
  dsimp only
  ext j
  rw [stream_complete_action_current]
  let r : ℂ := p.val 1
  let P := fun j => staticStreamJet w c cr crr (J j)
  let Q := fun j => staticStreamJet (-w) d dr drr (J j)
  have hO : orbit r (-w) d dr drr=orbit r w d dr drr := by simp [orbit]
  fin_cases j
  · change -1/((r^(2 : ℕ)-1)*r^(2 : ℕ))*(∑ i : Fin 2,
      (w*c*(J i).value*(streamAngularAction (p.val 3) Q i-streamMasterValue r (p.val 3) Q i)-
       (-w)*d*(J i).value*(streamAngularAction (p.val 3) P i-streamMasterValue r (p.val 3) P i))) =
      (w/(r^(2 : ℕ)*(r^(2 : ℕ)-1))*(c*orbit r w d dr drr+d*orbit r w c cr crr))*modeAngularSquare J
    dsimp only [P,Q]
    simp only [stream_orbit,hO,modeAngularSquare,Fin.sum_univ_succ]
    field_simp [hr,hR]
    ring
  · change (r^(2 : ℕ)-1)/r^(2 : ℕ)*(∑ i : Fin 2,
      (cr*(J i).value*(streamAngularAction (p.val 3) Q i-streamMasterValue r (p.val 3) Q i)-
       dr*(J i).value*(streamAngularAction (p.val 3) P i-streamMasterValue r (p.val 3) P i))) =
      ((r^(2 : ℕ)-1)/r^(2 : ℕ)*(dr*orbit r w c cr crr-cr*orbit r w d dr drr))*modeAngularSquare J
    dsimp only [P,Q]
    simp only [stream_orbit,hO,modeAngularSquare,Fin.sum_univ_succ]
    ring
  · change (p.val 3:ℂ)^(2 : ℕ)/(p.val 1:ℂ)^(2 : ℕ)*
      (-((p.val 1:ℂ)^(2 : ℕ)-1)*(cr*(J 1).value*(dr*(J 1).first 0-dr*(J 0).first 1)-
        dr*(J 1).value*(cr*(J 1).first 0-cr*(J 0).first 1))+
       (w*c*(J 1).value*((-w)*d*(J 1).first 0-(-w)*d*(J 0).first 1)-
        (-w)*d*(J 1).value*(w*c*(J 1).first 0-w*c*(J 0).first 1))/((p.val 1:ℂ)^(2 : ℕ)-1))=0
    ring
  · change (p.val 3:ℂ)^(2 : ℕ)/(p.val 1:ℂ)^(2 : ℕ)*
      (((p.val 1:ℂ)^(2 : ℕ)-1)*(cr*(J 0).value*(dr*(J 1).first 0-dr*(J 0).first 1)-
        dr*(J 0).value*(cr*(J 1).first 0-cr*(J 0).first 1))-
       (w*c*(J 0).value*((-w)*d*(J 1).first 0-(-w)*d*(J 0).first 1)-
        (-w)*d*(J 0).value*(w*c*(J 1).first 0-w*c*(J 0).first 1))/((p.val 1:ℂ)^(2 : ℕ)-1))=0
    ring

private theorem orbit_radial (r w lam f df F : ℂ) (hr : r ≠ 0) (hR : r^(2 : ℕ)-1 ≠ 0) :
    orbit r w (r*f) (f+r*df/(r^(2 : ℕ)-1))
      ((r*((w^(2 : ℕ)-lam*(r^(2 : ℕ)-1)/r^(2 : ℕ))*f-F)-2*df)/(r^(2 : ℕ)-1)^(2 : ℕ)) =
      r*(2-lam)*f-r^(3 : ℕ)/(r^(2 : ℕ)-1)*F := by
  unfold orbit
  field_simp [hr,hR]
  ring

/-- Exact complete Einstein current of opposite-frequency radial stream jets.
The source contact remains in both time and radial components. -/
theorem radial_mode_action (p : D4BMBackground.ExteriorPoint)
    (w lam f df g dg F : ℂ) (J : Fin 2 → ScalarTwoJet (Fin 2) ℂ) :
    let r : ℂ := p.val 1
    let P := fun j => radialStreamJet r w f df ((w^(2 : ℕ)-lam*(r^(2 : ℕ)-1)/r^(2 : ℕ))*f-F) (J j)
    let Q := fun j => radialStreamJet r (-w) g dg ((w^(2 : ℕ)-lam*(r^(2 : ℕ)-1)/r^(2 : ℕ))*g) (J j)
    (fun j => r^(2 : ℕ)/(p.val 3:ℂ)^(2 : ℕ)*actionSymplectic
      (D4BMBackground.jet r (p.val 3)) (streamMetricJet r P) (streamMetricJet r Q) j) =
    ![(-2*w*(lam-2)*f*g/(r^(2 : ℕ)-1)-w*r^(2 : ℕ)*g*F/(r^(2 : ℕ)-1)^(2 : ℕ))*modeAngularSquare J,
      (-(lam-2)*(dg*f-g*df)-(r*g+r^(2 : ℕ)*dg/(r^(2 : ℕ)-1))*F)*modeAngularSquare J,0,0] := by
  have hr : (p.val 1:ℂ) ≠ 0 := by exact_mod_cast (show p.val 1 ≠ 0 by linarith [p.property.1])
  have hR : (p.val 1:ℂ)^(2 : ℕ)-1 ≠ 0 := by
    exact_mod_cast (show (p.val 1)^(2 : ℕ)-1 ≠ 0 by nlinarith [p.property.1])
  dsimp only [radialStreamJet]
  rw [static_action,orbit_radial _ _ _ _ _ _ hr hR,
    ← sub_zero ((w^(2 : ℕ)-lam*((p.val 1:ℂ)^(2 : ℕ)-1)/(p.val 1:ℂ)^(2 : ℕ))*g),
    orbit_radial _ _ _ _ _ _ hr hR]
  apply congrArg₂ (fun a b : ℂ => (![a,b,0,0] : Fin 4 → ℂ))
  all_goals field_simp [hr,hR]
  all_goals ring

open ScalarTwoJet D4BMFundamentalScalarMetric

private theorem coordinate_partial {d : ℕ} (f : ℝ → ℂ) (k i : Fin d)
    (x : Fin d → ℝ) (hf : DifferentiableAt ℝ f (x k)) :
    coordDeriv i (fun y => f (y k)) x = if i=k then deriv f (x k) else 0 := by
  have hi : HasFDerivAt (fun y : Fin d → ℝ => y k)
      (ContinuousLinearMap.proj k : (Fin d → ℝ) →L[ℝ] ℝ) x := hasFDerivAt_apply k x
  have h := hf.hasDerivAt.hasFDerivAt.comp x hi
  change fderiv ℝ (f ∘ fun y => y k) x (Pi.single i 1) = _
  rw [h.fderiv]
  by_cases hi : i=k
  · subst i
    simp
  · simp [hi,Ne.symm hi]

private theorem coordinate_jet_real {d : ℕ} (f : ℝ → ℂ) (k : Fin d)
    (x : Fin d → ℝ) (hf : ContDiffAt ℝ 2 f (x k)) :
    ofField (fun y => f (y k)) x =
      ⟨f (x k),fun i => if i=k then deriv f (x k) else 0,
        fun i j => if i=k ∧ j=k then deriv (deriv f) (x k) else 0⟩ := by
  ext i j
  · rfl
  · exact coordinate_partial f k i x (hf.differentiableAt (by norm_num))
  · have he : coordDeriv j (fun y => f (y k)) =ᶠ[𝓝 x]
        (fun y => if j=k then deriv f (y k) else 0) := by
      have hn := (continuous_apply k).continuousAt.eventually (hf.eventually (by simp))
      filter_upwards [hn] with y hy
      exact coordinate_partial f k j y (hy.differentiableAt (by norm_num))
    change fderiv ℝ _ x (Pi.single i 1) = _
    rw [he.fderiv_eq]
    by_cases hj : j=k
    · subst j
      simp only [↓reduceIte,and_true]
      exact coordinate_partial (deriv f) k i x
        ((hf.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num))
    · simp [hj]

/-- The separated table is the actual two-jet of a time/radius/angular field at time zero. -/
theorem staticStreamJet_actual (w : ℂ) (h : ℝ → ℂ) (S : (Fin 2 → ℝ) → ℂ)
    (x : Fin 4 → ℝ) (hx : x 0=0) (hh : ContDiffAt ℝ 2 h (x 1))
    (hS : ContDiffAt ℝ 2 S (D4BMMetricReconstruction.angularPoint x)) :
    ofField (fun y => Complex.exp (w*(y 0:ℂ))*h (y 1)*
      S (D4BMMetricReconstruction.angularPoint y)) x =
    staticStreamJet w (h (x 1)) (deriv h (x 1)) (deriv (deriv h) (x 1))
      (ofField S (D4BMMetricReconstruction.angularPoint x)) := by
  have hc : ContDiffAt ℝ 2 (fun y : Fin 4 → ℝ => (y 0:ℂ)) x :=
    (Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ 0)).contDiffAt
  have ht : ContDiffAt ℝ 2 (fun y : Fin 4 → ℝ => Complex.exp (w*(y 0:ℂ))) x := (contDiffAt_const.mul hc).cexp
  have hr : ContDiffAt ℝ 2 (fun y : Fin 4 → ℝ => h (y 1)) x :=
    hh.comp x (contDiff_apply ℝ ℝ 1).contDiffAt
  have ha : ContDiffAt ℝ 2 (fun y : Fin 4 → ℝ => S (D4BMMetricReconstruction.angularPoint y)) x := by
    apply hS.comp x
    change ContDiffAt ℝ 2 (fun y : Fin 4 → ℝ => ![y 2,y 3]) x
    apply contDiffAt_pi.mpr
    intro i
    fin_cases i <;> exact (contDiff_apply ℝ ℝ _).contDiffAt
  rw [ofField_mul (ht.mul hr) ha,ofField_mul ht hr,coordinate_jet_real h 1 x hh,
    D4BMScalarLinearEquation.angular_lift_jet S x hS]
  have htime : ofField (fun y : Fin 4 → ℝ => Complex.exp (w*(y 0:ℂ))) x =
      compose ((constant w).mul (coordinateJet (x 0) 0)) 1 1 1 := by
    rw [ofField_comp (φ := Complex.exp) (g := fun y : Fin 4 → ℝ => w*(y 0:ℂ)) (x := x)
      (by fun_prop : ContDiffAt ℂ 2 Complex.exp (w*(x 0:ℂ))) (contDiffAt_const.mul hc),
      ofField_mul contDiffAt_const hc,ofField_constant,coordinate_jet]
    simp only [hx,Complex.ofReal_zero,mul_zero,Complex.exp_zero,Complex.deriv_exp]
  rw [htime]
  ext i j
  · simp [staticStreamJet,compose,ScalarTwoJet.mul,constant,coordinateJet,ofField]
  · fin_cases i <;> simp [staticStreamJet,compose,ScalarTwoJet.mul,constant,coordinateJet,ofField]
  · fin_cases i <;> fin_cases j <;>
      simp [staticStreamJet,compose,ScalarTwoJet.mul,constant,coordinateJet,ofField]
    all_goals first | rfl | (ring_nf; simp)


private theorem tortoise_C2 (r : ℝ) (hr : 1 < r) :
    ContDiffAt ℝ 2 D4BMIngoingCoordinates.tortoise r := by
  have hm : r-1 ≠ 0 := by linarith
  have hp : r+1 ≠ 0 := by linarith
  unfold D4BMIngoingCoordinates.tortoise
  fun_prop

theorem radiusLift_C2 (f : ℝ → ℂ) (r : ℝ) (hr : 1 < r)
    (hf : ContDiffAt ℝ 2 f (D4BMIngoingCoordinates.tortoise r)) :
    ContDiffAt ℝ 2 (radiusLift f) r :=
  Complex.ofRealCLM.contDiff.contDiffAt.mul (hf.comp r (tortoise_C2 r hr))

/-- Both ordinary derivatives of the reconstructed radius factor equal the differentiated table. -/
theorem radiusLift_deriv_values (f : ℝ → ℂ) (r : ℝ) (hr : 1 < r)
    (hf : ContDiffAt ℝ 2 f (D4BMIngoingCoordinates.tortoise r)) :
    deriv (radiusLift f) r=radiusLiftFirst f (deriv f) r ∧
      deriv (deriv (radiusLift f)) r=radiusLiftSecond (deriv f) (deriv (deriv f)) r := by
  have hd := radiusLift_derivatives f (deriv f) (deriv (deriv f)) r hr
    (hf.differentiableAt (by norm_num)).hasDerivAt
    ((hf.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasDerivAt
  refine ⟨hd.1.deriv,?_⟩
  have he : deriv (radiusLift f) =ᶠ[𝓝 r] radiusLiftFirst f (deriv f) := by
    have hnear := (tortoise_C2 r hr).continuousAt.eventually (hf.eventually (by simp))
    filter_upwards [hnear,isOpen_Ioi.mem_nhds hr] with y hy hyr
    exact (radiusLift_derivatives f (deriv f) (deriv (deriv f)) y hyr
      (hy.differentiableAt (by norm_num)).hasDerivAt
      ((hy.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasDerivAt).1.deriv
  exact he.deriv_eq.trans hd.2.deriv

/-- The original-radius radial table is the actual full coordinate two-jet, not supplied jet data. -/
theorem radialStreamJet_actual (w : ℂ) (f : ℝ → ℂ) (S : (Fin 2 → ℝ) → ℂ)
    (x : Fin 4 → ℝ) (hx : x 0=0) (hr : 1 < x 1)
    (hf : ContDiffAt ℝ 2 f (D4BMIngoingCoordinates.tortoise (x 1)))
    (hS : ContDiffAt ℝ 2 S (D4BMMetricReconstruction.angularPoint x)) :
    ofField (fun y => Complex.exp (w*(y 0:ℂ))*radiusLift f (y 1)*
      S (D4BMMetricReconstruction.angularPoint y)) x =
    radialStreamJet (x 1) w (f (D4BMIngoingCoordinates.tortoise (x 1)))
      (deriv f (D4BMIngoingCoordinates.tortoise (x 1)))
      (deriv (deriv f) (D4BMIngoingCoordinates.tortoise (x 1)))
      (ofField S (D4BMMetricReconstruction.angularPoint x)) := by
  rw [staticStreamJet_actual w (radiusLift f) S x hx (radiusLift_C2 f (x 1) hr hf) hS,
    (radiusLift_deriv_values f (x 1) hr hf).1,(radiusLift_deriv_values f (x 1) hr hf).2]
  rfl


/-- Full angular stream operator on the original angular two-jet. -/
def angularJetOperator (y : ℂ) (J : Fin 2 → ScalarTwoJet (Fin 2) ℂ) (i : Fin 2) : ℂ :=
  y^(2 : ℕ)*((J i).second 0 0+(J i).second 1 1)+
    2*y*(if i=0 then (J 0).first 1-(J 1).first 0 else (J 1).first 1+(J 0).first 0)

/-- The reconstructed master retains exactly the angular defect and complete radial forcing. -/
theorem radial_stream_master (r y w lam f df F : ℂ) (hr : r ≠ 0) (hR : r^(2 : ℕ)-1 ≠ 0)
    (J : Fin 2 → ScalarTwoJet (Fin 2) ℂ) (i : Fin 2) :
    streamMasterValue r y
      (fun j => radialStreamJet r w f df ((w^(2 : ℕ)-lam*(r^(2 : ℕ)-1)/r^(2 : ℕ))*f-F) (J j)) i =
      r*f*(angularJetOperator y J i-lam*(J i).value)-r^(3 : ℕ)/(r^(2 : ℕ)-1)*F*(J i).value := by
  let dd := (w^(2 : ℕ)-lam*(r^(2 : ℕ)-1)/r^(2 : ℕ))*f-F
  have h := stream_orbit r y w (r*f) (f+r*df/(r^(2 : ℕ)-1)) ((r*dd-2*df)/(r^(2 : ℕ)-1)^(2 : ℕ)) J i
  dsimp only [dd] at h
  rw [orbit_radial r w lam f df F hr hR] at h
  have ha : streamAngularAction y (fun j => radialStreamJet r w f df dd (J j)) i =
      r*f*(angularJetOperator y J i-2*(J i).value) := by
    fin_cases i <;> simp [radialStreamJet,staticStreamJet,streamAngularAction,angularJetOperator] <;> ring
  dsimp only [radialStreamJet,dd] at ha ⊢
  linear_combination ha-h


end
end RHTower.D4BMPhysicalModeAction
