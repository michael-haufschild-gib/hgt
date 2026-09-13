import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalOrbitCurrent

/-!
# Original continued reader equation and finite metric periods

The original left scalar satisfies its contact and angular equations at every
exterior time, for both continued radial normalizations. Substitution in the
actual metric-current identity gives scalar periods with explicit eigenvalue
coefficients and the complete original boundary flux. The temporal, cusp and
horizon limits are not interchanged here.
-/

open Set Filter Topology
open scoped ContDiff
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal
attribute [-instance] RCLike.innerProductSpace
namespace RHTower.D4BMOriginalReaderEquation
open GaloisForLFunctions.HTGeometry ScalarTwoJet
open D4BMPhysicalModeAction D4BMFundamentalScalarMetric D4BMMetricReconstruction
open D4BMOriginalAngularCurrent D4BMOriginalSourceContact D4BMIngoingCoordinates
open D4BMJointWave D4BMJointSource D4BMLeftModeRadialEquation
noncomputable section
private abbrev P := Fin 4 → ℝ
private abbrev F := P → ℂ

private theorem tortoise_neg (r : ℝ) (hr : 1<r) : tortoise r<0 := by
  have h := Real.log_lt_log (show 0<r-1 by linarith) (show r-1<r+1 by linarith)
  dsimp [tortoise]
  linarith

private theorem radius_inverse (r : ℝ) (hr : 1<r) : tortoiseRadius (tortoise r)=r := by
  let R := tortoiseRadius (tortoise r)
  have hR : 1<R := tortoiseRadius_exterior _ (tortoise_neg r hr)
  have h := tortoise_original_inverse (tortoise r) (tortoise_neg r hr)
  change tortoise R=tortoise r at h
  have hRm : R-1≠0 := by linarith
  have hRp : R+1≠0 := by linarith
  have hrm : r-1≠0 := by linarith
  have hrp : r+1≠0 := by linarith
  rw [tortoise,tortoise,← Real.log_div hRm hRp,← Real.log_div hrm hrp] at h
  have he := congrArg Real.exp (show Real.log ((R-1)/(R+1))=Real.log ((r-1)/(r+1)) by linarith)
  rw [Real.exp_log (div_pos (by linarith) (by linarith)),
    Real.exp_log (div_pos (by linarith) (by linarith))] at he
  field_simp [hRp,hrp] at he
  change R=r
  nlinarith

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

private theorem separated_jet (w : ℂ) (h : ℝ → ℂ) (S : (Fin 2 → ℝ) → ℂ)
    (x : Fin 4 → ℝ) (hh : ContDiffAt ℝ 2 h (x 1))
    (hS : ContDiffAt ℝ 2 S (D4BMMetricReconstruction.angularPoint x)) :
    ofField (fun y => Complex.exp (w*(y 0:ℂ))*h (y 1)*
      S (D4BMMetricReconstruction.angularPoint y)) x =
    staticStreamJet w (Complex.exp (w*(x 0:ℂ))*h (x 1))
      (Complex.exp (w*(x 0:ℂ))*deriv h (x 1))
      (Complex.exp (w*(x 0:ℂ))*deriv (deriv h) (x 1))
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
      compose ((constant w).mul (coordinateJet (x 0) 0))
        (Complex.exp (w*(x 0:ℂ))) (Complex.exp (w*(x 0:ℂ))) (Complex.exp (w*(x 0:ℂ))) := by
    rw [ofField_comp (φ := Complex.exp) (g := fun y : Fin 4 → ℝ => w*(y 0:ℂ)) (x := x)
      (by fun_prop : ContDiffAt ℂ 2 Complex.exp (w*(x 0:ℂ))) (contDiffAt_const.mul hc),
      ofField_mul contDiffAt_const hc,ofField_constant,coordinate_jet]
    simp only [Complex.deriv_exp]
  rw [htime]
  ext i j
  · simp [staticStreamJet,compose,ScalarTwoJet.mul,constant,coordinateJet,ofField]
  · fin_cases i <;> simp [staticStreamJet,compose,ScalarTwoJet.mul,constant,coordinateJet,ofField]
    all_goals first | rfl | (left; ring)
  · fin_cases i <;> fin_cases j <;>
      simp [staticStreamJet,compose,ScalarTwoJet.mul,constant,coordinateJet,ofField]
    all_goals first | rfl | (ring_nf; simp)


private theorem lift_values (q : XiZeroCopy) (side outer : Bool) (r : ℝ) (hr : 1<r) :
    deriv (radiusLift (profile q side outer)) r=
      radiusLiftFirst (profile q side outer) (profileFirst q side outer) r ∧
    deriv (deriv (radiusLift (profile q side outer))) r=
      radiusLiftSecond (profileFirst q side outer) (profileSecond q side outer) r := by
  have hd (R : ℝ) (hR : 1<R) := radius_derivatives q side outer ⟨tortoise R,tortoise_neg R hR⟩
  have hh (R : ℝ) (hR : 1<R) := hd R hR
  have hder (R : ℝ) (hR : 1<R) :
      deriv (radiusLift (profile q side outer)) R=
        radiusLiftFirst (profile q side outer) (profileFirst q side outer) R := by
    simpa only [radius_inverse R hR] using (hh R hR).1.deriv
  refine ⟨hder r hr,?_⟩
  have he : deriv (radiusLift (profile q side outer)) =ᶠ[𝓝 r]
      radiusLiftFirst (profile q side outer) (profileFirst q side outer) := by
    filter_upwards [isOpen_Ioi.mem_nhds hr] with R hR
    exact hder R hR
  exact he.deriv_eq.trans (by simpa only [radius_inverse r hr] using (hh r hr).2.1.deriv)

private def staticContact (r : ℂ) (J : ScalarTwoJet (Fin 4) ℂ) : ℂ :=
  -r^2*(r^2-1)*J.second 1 1+r^2/(r^2-1)*J.second 0 0-2*r*J.first 1

private theorem contact_toStatic (U : F) (x : P) (hr : 1<x 1) :
    scalarContact U x=staticContact (x 1)
      (D4BMIngoingFullCurrent.toStatic (x 1) (ofField U x)) := by
  have hf : (x 1:ℂ)^2-1≠0 := by exact_mod_cast (show x 1^2-1≠0 by nlinarith)
  change -(x 1:ℂ)^2*((x 1:ℂ)^2-1)*(ofField U x).second 1 1-
    (x 1:ℂ)^2*((ofField U x).second 0 1+(ofField U x).second 1 0)-
    2*(x 1:ℂ)*(ofField U x).first 1+2*(x 1:ℂ)*(ofField U x).first 0=_
  simp only [staticContact,D4BMIngoingFullCurrent.toStatic,ite_true,zero_ne_one,ite_false,add_zero,and_self]
  field_simp [hf]
  ring

private def staticScalar (q : XiZeroCopy) (side outer : Bool) (x : P) : ℂ :=
  Complex.exp (-frequency q side*(x 0:ℂ))*radiusLift (profile q side outer) (x 1)*
    D4BMLiteralCusp.scalar (physicalAngularParameter q) (angularPoint x)

private theorem reader_comp (q : XiZeroCopy) (side outer : Bool) :
    (fun z => leftScalar q side outer (D4BMActualIngoingCurrent.ingoingPoint z))=
      staticScalar q side outer := by
  funext z
  rw [leftScalar_value]
  simp [D4BMActualIngoingCurrent.ingoingPoint,staticScalar,angularPoint]

private theorem static_jet (q : XiZeroCopy) (side outer : Bool) (x : P)
    (hr : 1<x 1) (hy : 0<x 3) :
    ofField (staticScalar q side outer) x=
      staticStreamJet (-frequency q side)
        (Complex.exp (-frequency q side*(x 0:ℂ))*radiusLift (profile q side outer) (x 1))
        (Complex.exp (-frequency q side*(x 0:ℂ))*radiusLiftFirst (profile q side outer) (profileFirst q side outer) (x 1))
        (Complex.exp (-frequency q side*(x 0:ℂ))*radiusLiftSecond (profileFirst q side outer) (profileSecond q side outer) (x 1))
        (ofField (D4BMLiteralCusp.scalar (physicalAngularParameter q)) (angularPoint x)) := by
  have hs : ContDiffAt ℝ 2 (profile q side outer) (tortoise (x 1)) :=
    ((profile_smooth q side outer).contDiffAt (isOpen_Iio.mem_nhds (tortoise_neg _ hr))).of_le
      (WithTop.coe_le_coe.mpr le_top)
  have h := separated_jet (-frequency q side) (radiusLift (profile q side outer))
    (D4BMLiteralCusp.scalar (physicalAngularParameter q)) x
    (radiusLift_C2 _ _ hr hs) (D4BMLiteralCusp.scalar_contDiffAt _ 2 _ hy)
  rw [(lift_values q side outer _ hr).1,(lift_values q side outer _ hr).2] at h
  exact h

/-- The actual continued reader has the scalar Einstein contact prescribed by its
original radial equation, at every exterior time and both radial normalizations. -/
theorem left_scalar_contact (q : XiZeroCopy) (side outer : Bool) (x : P)
    (hr : 1<x 1) (hy : 0<x 3) :
    scalarContact (leftScalar q side outer) x=(eigenvalue q-2)*leftScalar q side outer x := by
  let z : P := ![x 0-tortoise (x 1),x 1,x 2,x 3]
  have hz : D4BMActualIngoingCurrent.ingoingPoint z=x := by
    ext i
    fin_cases i <;> simp [z,D4BMActualIngoingCurrent.ingoingPoint]
  have hj := D4BMActualIngoingCurrent.ofField_ingoing_comp
    (F := leftScalar q side outer) (x := z) hr
    (by simpa only [hz] using ((leftScalar_smooth q side outer x hr hy).of_le
      (show (2:ℕ∞ω)≤∞ from WithTop.coe_le_coe.mpr le_top)))
  rw [reader_comp,hz] at hj
  change ofField (staticScalar q side outer) z=
    D4BMIngoingFullCurrent.toStatic (x 1) (ofField (leftScalar q side outer) x) at hj
  have hv : staticScalar q side outer z=leftScalar q side outer x := congrArg (fun J => J.value) hj
  rw [contact_toStatic _ x hr,← hj,static_jet q side outer z hr hy,← hv]
  have he := (radius_master_defect q side outer ⟨tortoise (x 1),tortoise_neg _ hr⟩ 1 (eigenvalue q)).1
  simp only [radius_inverse _ hr,mul_one,sub_self,mul_zero] at he
  dsimp only [D4BMVectorStream.master] at he
  simp only [mul_one] at he
  change staticContact (x 1) (staticStreamJet (-frequency q side)
      (Complex.exp (-frequency q side*((x 0-tortoise (x 1):ℝ):ℂ))*radiusLift (profile q side outer) (x 1))
      (Complex.exp (-frequency q side*((x 0-tortoise (x 1):ℝ):ℂ))*radiusLiftFirst (profile q side outer) (profileFirst q side outer) (x 1))
      (Complex.exp (-frequency q side*((x 0-tortoise (x 1):ℝ):ℂ))*radiusLiftSecond (profileFirst q side outer) (profileSecond q side outer) (x 1))
      (ofField (D4BMLiteralCusp.scalar (physicalAngularParameter q)) (angularPoint x)))=_
  dsimp only [staticContact,staticStreamJet,ofField]
  dsimp [staticScalar,z,angularPoint]
  linear_combination -Complex.exp (-frequency q side*((x 0-tortoise (x 1):ℝ):ℂ))*
    D4BMLiteralCusp.scalar (physicalAngularParameter q) ![x 2,x 3]*he

private theorem reader_static_jet (q : XiZeroCopy) (side outer : Bool) (x : P)
    (hr : 1<x 1) (hy : 0<x 3) :
    D4BMIngoingFullCurrent.toStatic (x 1) (ofField (leftScalar q side outer) x)=
      ofField (staticScalar q side outer) (staticPoint x) := by
  have hz : D4BMActualIngoingCurrent.ingoingPoint (staticPoint x)=x := by
    ext i
    fin_cases i <;> simp [staticPoint,D4BMActualIngoingCurrent.ingoingPoint]
  have hs : ContDiffAt ℝ 2 (leftScalar q side outer) (D4BMActualIngoingCurrent.ingoingPoint (staticPoint x)) := by
    rw [hz]
    exact (leftScalar_smooth q side outer x hr hy).of_le (WithTop.coe_le_coe.mpr le_top)
  have hj := D4BMActualIngoingCurrent.ofField_ingoing_comp
    (F := leftScalar q side outer) (x := staticPoint x) hr hs
  rw [reader_comp,hz] at hj
  exact hj.symm

/-- The unchanged reader's angular eigenvalue survives the original ingoing chart. -/
theorem left_angular_equation (q : XiZeroCopy) (side outer : Bool) (x : P)
    (hr : 1<x 1) (hy : 0<x 3) :
    angularLap (leftScalar q side outer) x=eigenvalue q*leftScalar q side outer x := by
  have hj := reader_static_jet q side outer x hr hy
  have hv : leftScalar q side outer x=staticScalar q side outer (staticPoint x) := congrArg (fun J => J.value) hj
  rw [static_jet q side outer (staticPoint x) hr hy] at hj
  have he := congrArg (fun J : ScalarTwoJet (Fin 4) ℂ => (x 3:ℂ)^2*(J.second 2 2+J.second 3 3)) hj
  simp only [D4BMIngoingFullCurrent.toStatic,show (2:Fin 4)≠1 by decide,
    show (3:Fin 4)≠1 by decide,ite_false,and_self,add_zero] at he
  change angularLap (leftScalar q side outer) x=_ at he
  rw [he,hv]
  have hS := D4BMLiteralCusp.scalar_equation (physicalAngularParameter q) (angularPoint x) hy
  rw [D4BMHorizon.scalarLaplacian_eq _ _ hy] at hS
  let E : ℂ := Complex.exp (-frequency q side*((x 0-tortoise (x 1):ℝ):ℂ))
  let H : ℂ := radiusLift (profile q side outer) (x 1)
  let S := D4BMLiteralCusp.scalar (physicalAngularParameter q)
  change (x 3:ℂ)^2*(E*H*coordDeriv 0 (coordDeriv 0 S) (angularPoint x)+
    E*H*coordDeriv 1 (coordDeriv 1 S) (angularPoint x))=
    eigenvalue q*(E*H*S (angularPoint x))
  change (x 3:ℂ)^2*(coordDeriv 0 (coordDeriv 0 S) (angularPoint x)+
    coordDeriv 1 (coordDeriv 1 S) (angularPoint x))=
    -(1/4-physicalAngularParameter q^2)*S (angularPoint x) at hS
  dsimp only [eigenvalue]
  linear_combination (E*H)*hS

private theorem smooth_partial {f : F} {x : P} (hf : ContDiffAt ℝ ∞ f x) (i : Fin 4) :
    ContDiffAt ℝ ∞ (coordDeriv i f) x := coordDeriv_contDiffAt hf (by simp) i

private theorem smooth_two {f : F} {x : P} (hf : ContDiffAt ℝ ∞ f x) :
    ContDiffAt ℝ 2 f x := hf.of_le (WithTop.coe_le_coe.mpr le_top)

private theorem partial_coordinate (x : P) (i k : Fin 4) :
    coordDeriv i (fun y : P => (y k:ℂ)) x=if i=k then 1 else 0 := by
  have h := Complex.ofRealCLM.hasFDerivAt.comp x (hasFDerivAt_apply k x)
  change fderiv ℝ (Complex.ofRealCLM ∘ (fun y : P => y k)) x (Pi.single i 1)=_
  rw [h.fderiv]
  by_cases hi : i=k
  · subst i; simp
  · simp [hi,Ne.symm hi]

private theorem partial_triple {f : F} {x : P} (hf : ContDiffAt ℝ ∞ f x) (i k : Fin 4) :
    coordDeriv i (coordDeriv k (coordDeriv k f)) x=
      coordDeriv k (coordDeriv k (coordDeriv i f)) x := by
  rw [coordDeriv_comm (smooth_two (smooth_partial hf k)) i k]
  have he : coordDeriv i (coordDeriv k f) =ᶠ[𝓝 x] coordDeriv k (coordDeriv i f) := by
    filter_upwards [(smooth_two hf).eventually (by norm_num)] with z hz
    exact coordDeriv_comm hz i k
  change fderiv ℝ (coordDeriv i (coordDeriv k f)) x (Pi.single k 1)=_
  rw [he.fderiv_eq]

private theorem angularLap_partial {f : F} {x : P} (hf : ContDiffAt ℝ ∞ f x)
    (i : Fin 4) (hi : i≠3) :
    coordDeriv i (angularLap f) x=angularLap (coordDeriv i f) x := by
  have hYs : ContDiff ℝ ∞ (fun z : P => (z 3:ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ (3:Fin 4))
  have hY := hYs.differentiable (by simp) x
  have h2 := (smooth_partial (smooth_partial hf 2) 2).differentiableAt (by simp)
  have h3 := (smooth_partial (smooth_partial hf 3) 3).differentiableAt (by simp)
  change coordDeriv i (fun z => (z 3:ℂ)^2*
    (coordDeriv 2 (coordDeriv 2 f) z+coordDeriv 3 (coordDeriv 3 f) z)) x=_
  simp only [pow_two]
  have hYY : DifferentiableAt ℝ (fun z : P => (z 3:ℂ)*(z 3:ℂ)) x := hY.mul hY
  have hsum : DifferentiableAt ℝ (fun z => coordDeriv 2 (coordDeriv 2 f) z+
    coordDeriv 3 (coordDeriv 3 f) z) x := h2.add h3
  rw [coordDeriv_mul hYY hsum,coordDeriv_mul hY hY,
    partial_coordinate,if_neg hi,coordDeriv_add h2 h3,
    partial_triple hf i 2,partial_triple hf i 3]
  dsimp only [angularLap]
  ring


private theorem angularLap_const_mul (c : ℂ) {U : F} {x : P} (hU : ContDiffAt ℝ 2 U x) :
    angularLap (fun z => c*U z) x=c*angularLap U x := by
  have hj := ofField_mul (contDiffAt_const (c := c)) hU
  rw [ofField_constant] at hj
  have he := congrArg (fun J : ScalarTwoJet (Fin 4) ℂ => (x 3:ℂ)^2*(J.second 2 2+J.second 3 3)) hj
  change angularLap (fun z => c*U z) x=_ at he
  rw [he]
  simp only [ScalarTwoJet.mul,constant,zero_mul,add_zero,zero_add,ofField,angularLap]
  ring

private theorem angularLap_add {U V : F} {x : P}
    (hU : ContDiffAt ℝ 2 U x) (hV : ContDiffAt ℝ 2 V x) :
    angularLap (fun z => U z+V z) x=angularLap U x+angularLap V x := by
  have hj := ofField_add hU hV
  have he := congrArg (fun J : ScalarTwoJet (Fin 4) ℂ => (x 3:ℂ)^2*(J.second 2 2+J.second 3 3)) hj
  change angularLap (fun z => U z+V z) x=_ at he
  rw [he]
  simp only [ScalarTwoJet.add,ofField,angularLap]
  ring

private theorem angularLap_radial_mul (h : ℝ → ℂ) {U : F} {x : P}
    (hh : ContDiffAt ℝ 2 h (x 1)) (hU : ContDiffAt ℝ 2 U x) :
    angularLap (fun z => h (z 1)*U z) x=h (x 1)*angularLap U x := by
  have hh' : ContDiffAt ℝ 2 (fun z : P => h (z 1)) x :=
    hh.comp x (contDiff_apply ℝ ℝ (1:Fin 4)).contDiffAt
  have hj := ofField_mul hh' hU
  rw [coordinate_jet_real h 1 x hh] at hj
  have he := congrArg (fun J : ScalarTwoJet (Fin 4) ℂ => (x 3:ℂ)^2*(J.second 2 2+J.second 3 3)) hj
  change angularLap (fun z => h (z 1)*U z) x=_ at he
  rw [he]
  simp [ScalarTwoJet.mul,ofField,angularLap]
  ring

private theorem left_angular_germ (q : XiZeroCopy) (side outer : Bool) (x : P)
    (hr : 1<x 1) (hy : 0<x 3) :
    angularLap (leftScalar q side outer) =ᶠ[𝓝 x] fun z => eigenvalue q*leftScalar q side outer z := by
  filter_upwards [(isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hr,
    (isOpen_lt continuous_const (continuous_apply 3)).mem_nhds hy] with z hR hY
  exact left_angular_equation q side outer z hR hY

private theorem left_partial_angular (q : XiZeroCopy) (side outer : Bool) (x : P)
    (hr : 1<x 1) (hy : 0<x 3) (i : Fin 4) (hi : i≠3) :
    angularLap (coordDeriv i (leftScalar q side outer)) x=
      eigenvalue q*coordDeriv i (leftScalar q side outer) x := by
  have hs := leftScalar_smooth q side outer x hr hy
  have he := (left_angular_germ q side outer x hr hy).fderiv_eq (𝕜 := ℝ)
  have hd := congrArg (fun L : P →L[ℝ] ℂ => L (Pi.single i 1)) he
  change coordDeriv i (angularLap (leftScalar q side outer)) x=
    coordDeriv i (fun z => eigenvalue q*leftScalar q side outer z) x at hd
  rw [angularLap_partial hs i hi,coordDeriv_mul (differentiableAt_const (eigenvalue q))
    (hs.differentiableAt (by simp))] at hd
  simpa [coordDeriv] using hd

/-- Both reader factors in the physical temporal/radial currents have the same angular eigenvalue. -/
theorem left_orbit_angular (q : XiZeroCopy) (side outer : Bool) (x : P)
    (hr : 1<x 1) (hy : 0<x 3) (j : Fin 2) :
    angularLap (D4BMOriginalOrbitCurrent.orbitDerivative (leftScalar q side outer) j) x=
      eigenvalue q*D4BMOriginalOrbitCurrent.orbitDerivative (leftScalar q side outer) j x := by
  have hs := leftScalar_smooth q side outer x hr hy
  have h0 := smooth_two (smooth_partial hs 0)
  have h1 := smooth_two (smooth_partial hs 1)
  have hR : ContDiffAt ℝ 2 (fun R : ℝ => (R:ℂ)^2-1) (x 1) :=
    (Complex.ofRealCLM.contDiff.contDiffAt.pow 2).sub contDiffAt_const
  by_cases hj : j=0
  · subst j
    exact left_partial_angular q side outer x hr hy 1 (by decide)
  · have hfun : D4BMOriginalOrbitCurrent.orbitDerivative (leftScalar q side outer) j=
        fun z => ((z 1:ℂ)^2-1)*coordDeriv 1 (leftScalar q side outer) z+coordDeriv 0 (leftScalar q side outer) z := by
      funext z
      exact if_neg hj
    rw [hfun]
    change angularLap (fun z => ((z 1:ℂ)^2-1)*coordDeriv 1 (leftScalar q side outer) z+
      coordDeriv 0 (leftScalar q side outer) z) x=_
    have hR' : ContDiffAt ℝ 2 (fun z : P => ((z 1:ℂ)^2-1)*coordDeriv 1 (leftScalar q side outer) z) x := by
      simpa only [Function.comp_def] using (hR.comp x (contDiff_apply ℝ ℝ (1:Fin 4)).contDiffAt).mul h1
    rw [angularLap_add hR' h0,
      angularLap_radial_mul _ hR h1,left_partial_angular q side outer x hr hy 1 (by decide),
      left_partial_angular q side outer x hr hy 0 (by decide)]
    change _=eigenvalue q*(((x 1:ℂ)^2-1)*coordDeriv 1 (leftScalar q side outer) x+
      coordDeriv 0 (leftScalar q side outer) x)
    ring

/-- The actual reader contact remains in the same angular eigenspace. -/
theorem left_contact_angular (q : XiZeroCopy) (side outer : Bool) (x : P)
    (hr : 1<x 1) (hy : 0<x 3) :
    angularLap (scalarContact (leftScalar q side outer)) x=
      eigenvalue q*(eigenvalue q-2)*leftScalar q side outer x := by
  have hg : scalarContact (leftScalar q side outer) =ᶠ[𝓝 x]
      fun z => (eigenvalue q-2)*leftScalar q side outer z := by
    filter_upwards [(isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hr,
      (isOpen_lt continuous_const (continuous_apply 3)).mem_nhds hy] with z hR hY
    exact left_scalar_contact q side outer z hR hY
  have hj := ofField_germ hg
  have he := congrArg (fun J : ScalarTwoJet (Fin 4) ℂ => (x 3:ℂ)^2*(J.second 2 2+J.second 3 3)) hj
  change angularLap (scalarContact (leftScalar q side outer)) x=
    angularLap (fun z => (eigenvalue q-2)*leftScalar q side outer z) x at he
  rw [he,angularLap_const_mul _ (smooth_two (leftScalar_smooth q side outer x hr hy)),
    left_angular_equation q side outer x hr hy]
  ring


open MeasureTheory D4BMOriginalOrbitCurrent
open GaloisForLFunctions.RHTower SelbergMaassMean SelbergMaassTraceStokes SelbergModularDomainSlices

/-- Original bilinear scalar period on a finite modular domain, with hyperbolic area. -/
def scalarPeriod (A B : F) (p R Y : ℝ) : ℂ :=
  ∫ w in domain Y, A (slice p R (point w.1 w.2))*B (slice p R (point w.1 w.2))/(w.2:ℂ)^2

/-- Both scalar bulk densities in the actual metric transfer have explicit reader coefficients. -/
theorem original_reader_densities (q : XiZeroCopy) (side outer : Bool) (A : F) (x : P)
    (hr : 1<x 1) (hy : 0<x 3) (j : Fin 2) :
    scalarDensity A (scalarContact (leftScalar q side outer)) x=
      (eigenvalue q*(eigenvalue q-2))*(A x*leftScalar q side outer x/(x 3:ℂ)^2) ∧
    scalarDensity A (orbitDerivative (leftScalar q side outer) j) x=
      eigenvalue q*(A x*orbitDerivative (leftScalar q side outer) j x/(x 3:ℂ)^2) := by
  constructor
  · rw [scalarDensity_eq _ _ _ hy,left_contact_angular q side outer x hr hy]
    ring
  · rw [scalarDensity_eq _ _ _ hy,left_orbit_angular q side outer x hr hy j]
    ring

/-- The actual finite-height temporal/radial metric action is an explicit original
scalar-period combination plus its complete original angular boundary flux. -/
theorem original_metric_scalar_integral (q r : XiZeroCopy) (branch side outer : Bool) (amp : ℂ)
    (p R : ℝ) (hp : 0<p) (hr : 1<R) {Y : ℝ} (hY : 1≤Y) (j : Fin 2) :
    let U := sourceScalar q branch amp
    let W := leftScalar r side outer
    let A := orbitDerivative U j
    let D := forcedContact q branch amp
    let E := orbitDerivative W j
    (∫ w in domain Y, metricDensity q r branch side outer amp j (slice p R (point w.1 w.2)))+
      1/(R:ℂ)^2*((eigenvalue r*(eigenvalue r-2))*scalarPeriod A W p R Y-
        eigenvalue r*scalarPeriod D E p R Y)=
      1/(R:ℂ)^2*(boundary (transfer A (scalarContact W) 0) (transfer A (scalarContact W) 1) p R Y-
        boundary (transfer D E 0) (transfer D E 1) p R Y) := by
  dsimp only
  have h := original_metric_integral q r branch side outer amp p R hp hr hY j
  dsimp only at h
  have hfirst (A : F) :
      (∫ w in domain Y, scalarDensity A (scalarContact (leftScalar r side outer)) (slice p R (point w.1 w.2)))=
      (eigenvalue r*(eigenvalue r-2))*scalarPeriod A (leftScalar r side outer) p R Y := by
    rw [scalarPeriod,← integral_const_mul]
    apply setIntegral_congr_fun (isCompact_domain Y).measurableSet
    intro w hw
    have hy : 0<(point w.1 w.2).im := by simpa [point] using (show 0<w.2 by linarith [hw.1.2.1])
    simpa [slice,point] using (original_reader_densities r side outer A (slice p R (point w.1 w.2)) hr hy j).1
  have hsecond (A : F) :
      (∫ w in domain Y, scalarDensity A (orbitDerivative (leftScalar r side outer) j) (slice p R (point w.1 w.2)))=
      eigenvalue r*scalarPeriod A (orbitDerivative (leftScalar r side outer) j) p R Y := by
    rw [scalarPeriod,← integral_const_mul]
    apply setIntegral_congr_fun (isCompact_domain Y).measurableSet
    intro w hw
    have hy : 0<(point w.1 w.2).im := by simpa [point] using (show 0<w.2 by linarith [hw.1.2.1])
    simpa [slice,point] using (original_reader_densities r side outer A (slice p R (point w.1 w.2)) hr hy j).2
  rw [hfirst,hsecond] at h
  exact h

end
end RHTower.D4BMOriginalReaderEquation
