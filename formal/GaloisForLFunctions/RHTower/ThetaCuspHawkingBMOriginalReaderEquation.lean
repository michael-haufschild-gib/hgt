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
  -r^(2 : ℕ)*(r^(2 : ℕ)-1)*J.second 1 1+r^(2 : ℕ)/(r^(2 : ℕ)-1)*J.second 0 0-2*r*J.first 1

private theorem contact_toStatic (U : F) (x : P) (hr : 1<x 1) :
    scalarContact U x=staticContact (x 1)
      (D4BMIngoingFullCurrent.toStatic (x 1) (ofField U x)) := by
  have hf : (x 1:ℂ)^(2 : ℕ)-1≠0 := by exact_mod_cast (show x 1^(2 : ℕ)-1≠0 by nlinarith)
  change -(x 1:ℂ)^(2 : ℕ)*((x 1:ℂ)^(2 : ℕ)-1)*(ofField U x).second 1 1-
    (x 1:ℂ)^(2 : ℕ)*((ofField U x).second 0 1+(ofField U x).second 1 0)-
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
  have he := congrArg (fun J : ScalarTwoJet (Fin 4) ℂ => (x 3:ℂ)^(2 : ℕ)*(J.second 2 2+J.second 3 3)) hj
  simp only [D4BMIngoingFullCurrent.toStatic,show (2:Fin 4)≠1 by decide,
    show (3:Fin 4)≠1 by decide,ite_false,and_self,add_zero] at he
  change angularLap (leftScalar q side outer) x=_ at he
  rw [he,hv]
  have hS := D4BMLiteralCusp.scalar_equation (physicalAngularParameter q) (angularPoint x) hy
  rw [D4BMHorizon.scalarLaplacian_eq _ _ hy] at hS
  let E : ℂ := Complex.exp (-frequency q side*((x 0-tortoise (x 1):ℝ):ℂ))
  let H : ℂ := radiusLift (profile q side outer) (x 1)
  let S := D4BMLiteralCusp.scalar (physicalAngularParameter q)
  change (x 3:ℂ)^(2 : ℕ)*(E*H*coordDeriv 0 (coordDeriv 0 S) (angularPoint x)+
    E*H*coordDeriv 1 (coordDeriv 1 S) (angularPoint x))=
    eigenvalue q*(E*H*S (angularPoint x))
  change (x 3:ℂ)^(2 : ℕ)*(coordDeriv 0 (coordDeriv 0 S) (angularPoint x)+
    coordDeriv 1 (coordDeriv 1 S) (angularPoint x))=
    -(1/4-physicalAngularParameter q^(2 : ℕ))*S (angularPoint x) at hS
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
  change coordDeriv i (fun z => (z 3:ℂ)^(2 : ℕ)*
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
  have he := congrArg (fun J : ScalarTwoJet (Fin 4) ℂ => (x 3:ℂ)^(2 : ℕ)*(J.second 2 2+J.second 3 3)) hj
  change angularLap (fun z => c*U z) x=_ at he
  rw [he]
  simp only [ScalarTwoJet.mul,constant,zero_mul,add_zero,zero_add,ofField,angularLap]
  ring

private theorem angularLap_add {U V : F} {x : P}
    (hU : ContDiffAt ℝ 2 U x) (hV : ContDiffAt ℝ 2 V x) :
    angularLap (fun z => U z+V z) x=angularLap U x+angularLap V x := by
  have hj := ofField_add hU hV
  have he := congrArg (fun J : ScalarTwoJet (Fin 4) ℂ => (x 3:ℂ)^(2 : ℕ)*(J.second 2 2+J.second 3 3)) hj
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
  have he := congrArg (fun J : ScalarTwoJet (Fin 4) ℂ => (x 3:ℂ)^(2 : ℕ)*(J.second 2 2+J.second 3 3)) hj
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
  have hR : ContDiffAt ℝ 2 (fun R : ℝ => (R:ℂ)^(2 : ℕ)-1) (x 1) :=
    (Complex.ofRealCLM.contDiff.contDiffAt.pow 2).sub contDiffAt_const
  by_cases hj : j=0
  · subst j
    exact left_partial_angular q side outer x hr hy 1 (by decide)
  · have hfun : D4BMOriginalOrbitCurrent.orbitDerivative (leftScalar q side outer) j=
        fun z => ((z 1:ℂ)^(2 : ℕ)-1)*coordDeriv 1 (leftScalar q side outer) z+coordDeriv 0 (leftScalar q side outer) z := by
      funext z
      exact if_neg hj
    rw [hfun]
    change angularLap (fun z => ((z 1:ℂ)^(2 : ℕ)-1)*coordDeriv 1 (leftScalar q side outer) z+
      coordDeriv 0 (leftScalar q side outer) z) x=_
    have hR' : ContDiffAt ℝ 2 (fun z : P => ((z 1:ℂ)^(2 : ℕ)-1)*coordDeriv 1 (leftScalar q side outer) z) x := by
      simpa only [Function.comp_def] using (hR.comp x (contDiff_apply ℝ ℝ (1:Fin 4)).contDiffAt).mul h1
    rw [angularLap_add hR' h0,
      angularLap_radial_mul _ hR h1,left_partial_angular q side outer x hr hy 1 (by decide),
      left_partial_angular q side outer x hr hy 0 (by decide)]
    change _=eigenvalue q*(((x 1:ℂ)^(2 : ℕ)-1)*coordDeriv 1 (leftScalar q side outer) x+
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
  have he := congrArg (fun J : ScalarTwoJet (Fin 4) ℂ => (x 3:ℂ)^(2 : ℕ)*(J.second 2 2+J.second 3 3)) hj
  change angularLap (scalarContact (leftScalar q side outer)) x=
    angularLap (fun z => (eigenvalue q-2)*leftScalar q side outer z) x at he
  rw [he,angularLap_const_mul _ (smooth_two (leftScalar_smooth q side outer x hr hy)),
    left_angular_equation q side outer x hr hy]
  ring


open MeasureTheory D4BMOriginalOrbitCurrent
open GaloisForLFunctions.RHTower SelbergMaassMean SelbergMaassTraceStokes SelbergModularDomainSlices

/-- Original bilinear scalar period on a finite modular domain, with hyperbolic area. -/
def scalarPeriod (A B : F) (p R Y : ℝ) : ℂ :=
  ∫ w in domain Y, A (slice p R (point w.1 w.2))*B (slice p R (point w.1 w.2))/(w.2:ℂ)^(2 : ℕ)

/-- Both scalar bulk densities in the actual metric transfer have explicit reader coefficients. -/
theorem original_reader_densities (q : XiZeroCopy) (side outer : Bool) (A : F) (x : P)
    (hr : 1<x 1) (hy : 0<x 3) (j : Fin 2) :
    scalarDensity A (scalarContact (leftScalar q side outer)) x=
      (eigenvalue q*(eigenvalue q-2))*(A x*leftScalar q side outer x/(x 3:ℂ)^(2 : ℕ)) ∧
    scalarDensity A (orbitDerivative (leftScalar q side outer) j) x=
      eigenvalue q*(A x*orbitDerivative (leftScalar q side outer) j x/(x 3:ℂ)^(2 : ℕ)) := by
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
      1/(R:ℂ)^(2 : ℕ)*((eigenvalue r*(eigenvalue r-2))*scalarPeriod A W p R Y-
        eigenvalue r*scalarPeriod D E p R Y)=
      1/(R:ℂ)^(2 : ℕ)*(boundary (transfer A (scalarContact W) 0) (transfer A (scalarContact W) 1) p R Y-
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


private abbrev A := Fin 2 → ℝ

/-- The original radial mode with its temporal frequency left independent. -/
abbrev modeProfile (q : XiZeroCopy) (w : ℂ) (outer : Bool) : ℝ → ℂ :=
  tortoiseMode outer w (physicalRadialFrequency q)
private abbrev modeFirst (q : XiZeroCopy) (w : ℂ) (outer : Bool) : ℝ → ℂ :=
  tortoiseModeFirst outer w (physicalRadialFrequency q)
private def modePotential (q : XiZeroCopy) (w : ℂ) (t : ℝ) : ℂ :=
  w^(2 : ℕ)-eigenvalue q*(horizonCoordinate t:ℂ)
private def modeSecond (q : XiZeroCopy) (w : ℂ) (outer : Bool) (t : ℝ) : ℂ :=
  modePotential q w t*modeProfile q w outer t

private theorem mode_derivatives (q : XiZeroCopy) (w : ℂ) (hw : w.im≠0)
    (outer : Bool) (t : Iio (0:ℝ)) :
    HasDerivAt (modeProfile q w outer) (modeFirst q w outer t) t ∧
    HasDerivAt (modeFirst q w outer) (modeSecond q w outer t) t := by
  have hd : HasDerivAt (modeProfile q w outer) (modeFirst q w outer t) t ∧
      HasDerivAt (modeFirst q w outer) (tortoiseModeSecond outer w (physicalRadialFrequency q) t) t := by
    cases outer
    · exact tortoiseMode_hasDerivAt_continued w (physicalRadialFrequency q) t t.property
    · have h := D4BMLaplaceRadial.normalizable_derivatives_continued
        (w:=w) (chi:=physicalRadialFrequency q) (horizonCoordinate_interior t t.property)
      have hc := horizonCoordinate_hasDerivAt t
      constructor
      · simpa only [modeProfile,modeFirst,tortoiseMode,tortoiseModeFirst,radialMode,radialModeFirst,
          if_true,Function.comp_def,Complex.real_smul] using! h.1.scomp (t:ℝ) hc
      · apply (((coordinateFirst_hasDerivAt t).ofReal_comp).mul (h.2.scomp (t:ℝ) hc)).congr_deriv
        dsimp only [tortoiseModeSecond,radialModeFirst,radialModeSecond,if_true,Function.comp_apply]
        simp only [Complex.real_smul,↓reduceIte]
        ring
  have he : tortoiseModeSecond outer w (physicalRadialFrequency q) t=
      (w^(2 : ℕ)+(horizonCoordinate t:ℂ)*(1/4+physicalRadialFrequency q^(2 : ℕ)))*modeProfile q w outer t := by
    cases outer
    · exact tortoiseMode_equation_continued w (physicalRadialFrequency q) hw t t.property
    · have hz := horizonCoordinate_interior t t.property
      have h := D4BMLaplaceRadial.normalizable_equation_continued (w:=w)
        (chi:=physicalRadialFrequency q) hz
      dsimp only [D4BMPhysicalMaster.radialJet] at h
      rw [mul_pow,Complex.I_sq] at h
      have hz0 : (horizonCoordinate t:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hz.1.ne'
      field_simp [hz0] at h
      dsimp only [modeProfile,tortoiseMode,tortoiseModeSecond,radialMode,radialModeFirst,
        radialModeSecond,if_true,coordinateFirst,coordinateSecond]
      have hu : (radialUnit t:ℂ)^(2 : ℕ)=1-(horizonCoordinate t:ℂ) := by
        simp only [horizonCoordinate,Complex.ofReal_sub,Complex.ofReal_one,Complex.ofReal_pow]
        ring
      push_cast
      simp only [mul_pow,hu,↓reduceIte] at h ⊢
      linear_combination (1/8:ℂ)*h
  refine ⟨hd.1,hd.2.congr_deriv ?_⟩
  rw [he,physicalRadialFrequency_parameter]
  dsimp [modeSecond,modePotential,eigenvalue]
  ring

/-- The same physical family is smooth in spacetime at every nonreal frequency,
covering the convergence band and both original fundamental resonances. -/
theorem modeProfile_smooth (q : XiZeroCopy) (w : ℂ) (hw : w.im≠0) (outer : Bool) :
    ContDiffOn ℝ ∞ (modeProfile q w outer) (Iio (0:ℝ)) := by
  have hv : ContDiff ℝ ∞ (modePotential q w) := by
    have hc (t : ℝ) : Real.cosh t≠0 := (Real.cosh_pos t).ne'
    unfold modePotential horizonCoordinate radialUnit
    fun_prop
  apply TwistedRadial.contDiffOn_of_linear_ode isOpen_Iio (modeProfile q w outer)
    (modeFirst q w outer) (fun _ => 0) (modePotential q w) (fun _ => 0)
    contDiffOn_const hv.contDiffOn contDiffOn_const
  · intro t ht
    exact (mode_derivatives q w hw outer ⟨t,ht⟩).1
  · intro t ht
    simpa only [zero_mul,zero_add,add_zero,modeSecond] using!
      (mode_derivatives q w hw outer ⟨t,ht⟩).2

private def modeTimeRadius : P →L[ℝ] A :=
  ContinuousLinearMap.pi ![ContinuousLinearMap.proj 0,ContinuousLinearMap.proj 1]

/-- Actual ingoing amplitude of the independently varying physical reader. -/
def modeAmplitude (q : XiZeroCopy) (w : ℂ) (outer : Bool) (z : A) : ℂ :=
  Complex.exp (-w*((z 0-tortoise (z 1)):ℂ))*radiusLift (modeProfile q w outer) (z 1)

/-- The physical scalar reader family retains its complete original angular field. -/
def modeScalar (q : XiZeroCopy) (w : ℂ) (outer : Bool) (x : P) : ℂ :=
  modeAmplitude q w outer (modeTimeRadius x)*
    D4BMLiteralCusp.scalar (physicalAngularParameter q) (angularPoint x)

/-- Explicit original coordinates of the varying-frequency scalar reader. -/
theorem modeScalar_value (q : XiZeroCopy) (w : ℂ) (outer : Bool) (x : P) :
    modeScalar q w outer x=Complex.exp (-w*((x 0-tortoise (x 1)):ℂ))*
      radiusLift (modeProfile q w outer) (x 1)*
      D4BMLiteralCusp.scalar (physicalAngularParameter q) (angularPoint x) := by
  simp [modeScalar,modeAmplitude,modeTimeRadius]

/-- Specializing the family returns the unchanged original QNM reader exactly. -/
theorem modeScalar_specialize (q : XiZeroCopy) (side outer : Bool) :
    modeScalar q (frequency q side) outer=leftScalar q side outer := rfl

private theorem modeAmplitude_smooth (q : XiZeroCopy) (w : ℂ) (hw : w.im≠0)
    (outer : Bool) (z : A) (hr : 1<z 1) : ContDiffAt ℝ ∞ (modeAmplitude q w outer) z := by
  have ht : ContDiffAt ℝ ∞ tortoise (z 1) := by
    have hm : z 1-1≠0 := by linarith
    have hp : z 1+1≠0 := by linarith
    unfold tortoise
    fun_prop
  have htR := ht.comp z (contDiff_apply ℝ ℝ (1:Fin 2)).contDiffAt
  have hP := (modeProfile_smooth q w hw outer).contDiffAt (isOpen_Iio.mem_nhds (tortoise_neg _ hr))
  have hR : ContDiffAt ℝ ∞ (fun y : A => (y 1:ℂ)) z :=
    (Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ (1:Fin 2))).contDiffAt
  have hc := Complex.ofRealCLM.contDiff.contDiffAt.comp z
    ((contDiff_apply ℝ ℝ (0:Fin 2)).contDiffAt.sub htR)
  have hE : ContDiffAt ℝ ∞ (fun y : A => Complex.exp (-w*((y 0-tortoise (y 1)):ℂ))) z := by
    simpa [Function.comp_def] using (contDiffAt_const (c:=-w) |>.mul hc).cexp
  have hv : ContDiffAt ℝ ∞ (fun y : A => modeProfile q w outer (tortoise (y 1))) z :=
    ContDiffAt.comp (g := modeProfile q w outer) (f := fun y : A => tortoise (y 1)) z hP htR
  change ContDiffAt ℝ ∞ (fun y : A =>
    Complex.exp (-w*((y 0-tortoise (y 1)):ℂ))*((y 1:ℂ)*modeProfile q w outer (tortoise (y 1)))) z
  exact hE.mul (hR.mul hv)

private theorem modeAngular_smooth : ContDiff ℝ ∞ angularPoint := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> exact contDiff_apply ℝ ℝ _

/-- Actual spacetime regularity of the full independent-frequency scalar reader. -/
theorem modeScalar_smooth (q : XiZeroCopy) (w : ℂ) (hw : w.im≠0) (outer : Bool)
    (x : P) (hr : 1<x 1) (hy : 0<x 3) : ContDiffAt ℝ ∞ (modeScalar q w outer) x := by
  have hA := (modeAmplitude_smooth q w hw outer (modeTimeRadius x) hr).comp x
    modeTimeRadius.contDiff.contDiffAt
  have hS : ContDiffAt ℝ ∞ (D4BMLiteralCusp.scalar (physicalAngularParameter q)) (angularPoint x) :=
    (D4BMAngularSeries.cuspLeg_contDiffOn .scalar (physicalAngularParameter q)).contDiffAt
      ((isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hy)
  exact hA.mul (hS.comp x modeAngular_smooth.contDiffAt)

private def modeStaticScalar (q : XiZeroCopy) (w : ℂ) (outer : Bool) (x : P) : ℂ :=
  Complex.exp (-w*(x 0:ℂ))*radiusLift (modeProfile q w outer) (x 1)*
    D4BMLiteralCusp.scalar (physicalAngularParameter q) (angularPoint x)

private theorem mode_comp (q : XiZeroCopy) (w : ℂ) (outer : Bool) :
    (fun z => modeScalar q w outer (D4BMActualIngoingCurrent.ingoingPoint z))=
      modeStaticScalar q w outer := by
  funext z
  simp [modeScalar,modeAmplitude,modeTimeRadius,D4BMActualIngoingCurrent.ingoingPoint,
    modeStaticScalar,angularPoint]

private theorem mode_lift_values (q : XiZeroCopy) (w : ℂ) (hw : w.im≠0) (outer : Bool)
    (r : ℝ) (hr : 1<r) :
    deriv (radiusLift (modeProfile q w outer)) r=radiusLiftFirst (modeProfile q w outer) (modeFirst q w outer) r ∧
    deriv (deriv (radiusLift (modeProfile q w outer))) r=radiusLiftSecond (modeFirst q w outer) (modeSecond q w outer) r := by
  have hd (R : ℝ) (hR : 1<R) := radiusLift_derivatives (modeProfile q w outer) (modeFirst q w outer)
    (modeSecond q w outer) R hR (mode_derivatives q w hw outer ⟨tortoise R,tortoise_neg R hR⟩).1
      (mode_derivatives q w hw outer ⟨tortoise R,tortoise_neg R hR⟩).2
  refine ⟨(hd r hr).1.deriv,?_⟩
  have he : deriv (radiusLift (modeProfile q w outer))=ᶠ[𝓝 r]
      radiusLiftFirst (modeProfile q w outer) (modeFirst q w outer) := by
    filter_upwards [isOpen_Ioi.mem_nhds hr] with R hR
    exact (hd R hR).1.deriv
  exact he.deriv_eq.trans (hd r hr).2.deriv

private theorem mode_static_jet (q : XiZeroCopy) (w : ℂ) (hw : w.im≠0) (outer : Bool)
    (x : P) (hr : 1<x 1) (hy : 0<x 3) :
    ofField (modeStaticScalar q w outer) x=
      staticStreamJet (-w)
        (Complex.exp (-w*(x 0:ℂ))*radiusLift (modeProfile q w outer) (x 1))
        (Complex.exp (-w*(x 0:ℂ))*radiusLiftFirst (modeProfile q w outer) (modeFirst q w outer) (x 1))
        (Complex.exp (-w*(x 0:ℂ))*radiusLiftSecond (modeFirst q w outer) (modeSecond q w outer) (x 1))
        (ofField (D4BMLiteralCusp.scalar (physicalAngularParameter q)) (angularPoint x)) := by
  have hs : ContDiffAt ℝ 2 (modeProfile q w outer) (tortoise (x 1)) :=
    ((modeProfile_smooth q w hw outer).contDiffAt (isOpen_Iio.mem_nhds (tortoise_neg _ hr))).of_le
      (WithTop.coe_le_coe.mpr le_top)
  have h := separated_jet (-w) (radiusLift (modeProfile q w outer))
    (D4BMLiteralCusp.scalar (physicalAngularParameter q)) x
    (radiusLift_C2 _ _ hr hs) (D4BMLiteralCusp.scalar_contDiffAt _ 2 _ hy)
  rw [(mode_lift_values q w hw outer _ hr).1,(mode_lift_values q w hw outer _ hr).2] at h
  exact h

/-- The scalar contact is derived from the original radial equation for every nonreal temporal frequency. -/
theorem mode_scalar_contact (q : XiZeroCopy) (w : ℂ) (hw : w.im≠0) (outer : Bool)
    (x : P) (hr : 1<x 1) (hy : 0<x 3) :
    scalarContact (modeScalar q w outer) x=(eigenvalue q-2)*modeScalar q w outer x := by
  let z : P := ![x 0-tortoise (x 1),x 1,x 2,x 3]
  have hz : D4BMActualIngoingCurrent.ingoingPoint z=x := by
    ext i
    fin_cases i <;> simp [z,D4BMActualIngoingCurrent.ingoingPoint]
  have hj := D4BMActualIngoingCurrent.ofField_ingoing_comp
    (F:=modeScalar q w outer) (x:=z) hr
    (by simpa only [hz] using ((modeScalar_smooth q w hw outer x hr hy).of_le
      (show (2:ℕ∞ω)≤∞ from WithTop.coe_le_coe.mpr le_top)))
  rw [mode_comp,hz] at hj
  change ofField (modeStaticScalar q w outer) z=
    D4BMIngoingFullCurrent.toStatic (x 1) (ofField (modeScalar q w outer) x) at hj
  have hv : modeStaticScalar q w outer z=modeScalar q w outer x := congrArg (fun J => J.value) hj
  rw [contact_toStatic _ x hr,← hj,mode_static_jet q w hw outer z hr hy,← hv]
  have hR : (x 1:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (by linarith)
  have hf : (x 1:ℂ)^(2 : ℕ)-1≠0 := by exact_mod_cast (show x 1^(2 : ℕ)-1≠0 by nlinarith)
  have hi : horizonCoordinate (tortoise (x 1))=((x 1)^(2 : ℕ)-1)/(x 1)^(2 : ℕ) := by
    have h : (horizonCoordinate (tortoise (x 1)):ℂ)=((x 1:ℂ)^(2 : ℕ)-1)/(x 1:ℂ)^(2 : ℕ) := by
      rw [horizonCoordinate_jointWeight _ (tortoise_neg _ hr),
        angularWeight_original_coefficient _ (tortoise_neg _ hr),radius_inverse _ hr]
    exact_mod_cast h
  dsimp only [staticContact,staticStreamJet,ofField,modeSecond,modePotential]
  dsimp [modeStaticScalar,z,angularPoint,radiusLift,radiusLiftFirst,radiusLiftSecond]
  dsimp only [modeSecond,modePotential]
  rw [hi]
  push_cast
  field_simp [hR,hf]
  ring


private theorem mode_reader_static_jet (q : XiZeroCopy) (w : ℂ) (hw : w.im≠0)
    (outer : Bool) (x : P) (hr : 1<x 1) (hy : 0<x 3) :
    D4BMIngoingFullCurrent.toStatic (x 1) (ofField (modeScalar q w outer) x)=
      ofField (modeStaticScalar q w outer) (staticPoint x) := by
  have hz : D4BMActualIngoingCurrent.ingoingPoint (staticPoint x)=x := by
    ext i
    fin_cases i <;> simp [staticPoint,D4BMActualIngoingCurrent.ingoingPoint]
  have hs : ContDiffAt ℝ 2 (modeScalar q w outer) (D4BMActualIngoingCurrent.ingoingPoint (staticPoint x)) := by
    rw [hz]
    exact (modeScalar_smooth q w hw outer x hr hy).of_le (WithTop.coe_le_coe.mpr le_top)
  have hj := D4BMActualIngoingCurrent.ofField_ingoing_comp (F:=modeScalar q w outer)
    (x:=staticPoint x) hr hs
  rw [mode_comp,hz] at hj
  exact hj.symm

/-- The literal angular equation holds throughout the independently varying temporal family. -/
theorem mode_angular_equation (q : XiZeroCopy) (w : ℂ) (hw : w.im≠0)
    (outer : Bool) (x : P) (hr : 1<x 1) (hy : 0<x 3) :
    angularLap (modeScalar q w outer) x=eigenvalue q*modeScalar q w outer x := by
  have hj := mode_reader_static_jet q w hw outer x hr hy
  have hv : modeScalar q w outer x=modeStaticScalar q w outer (staticPoint x) := congrArg (fun J => J.value) hj
  rw [mode_static_jet q w hw outer (staticPoint x) hr hy] at hj
  have he := congrArg (fun J : ScalarTwoJet (Fin 4) ℂ => (x 3:ℂ)^(2 : ℕ)*(J.second 2 2+J.second 3 3)) hj
  simp only [D4BMIngoingFullCurrent.toStatic,show (2:Fin 4)≠1 by decide,
    show (3:Fin 4)≠1 by decide,ite_false,and_self,add_zero] at he
  change angularLap (modeScalar q w outer) x=_ at he
  rw [he,hv]
  have hS := D4BMLiteralCusp.scalar_equation (physicalAngularParameter q) (angularPoint x) hy
  rw [D4BMHorizon.scalarLaplacian_eq _ _ hy] at hS
  let E : ℂ := Complex.exp (-w*((x 0-tortoise (x 1):ℝ):ℂ))
  let H : ℂ := radiusLift (modeProfile q w outer) (x 1)
  let S := D4BMLiteralCusp.scalar (physicalAngularParameter q)
  change (x 3:ℂ)^(2 : ℕ)*(E*H*coordDeriv 0 (coordDeriv 0 S) (angularPoint x)+
    E*H*coordDeriv 1 (coordDeriv 1 S) (angularPoint x))=eigenvalue q*(E*H*S (angularPoint x))
  change (x 3:ℂ)^(2 : ℕ)*(coordDeriv 0 (coordDeriv 0 S) (angularPoint x)+
    coordDeriv 1 (coordDeriv 1 S) (angularPoint x))= -(1/4-physicalAngularParameter q^(2 : ℕ))*S (angularPoint x) at hS
  dsimp only [eigenvalue]
  linear_combination (E*H)*hS

/-- The derivative is taken in the original ingoing clock, with the physical sign. -/
theorem mode_time_derivative (q : XiZeroCopy) (w : ℂ) (hw : w.im≠0)
    (outer : Bool) (x : P) (hr : 1<x 1) (hy : 0<x 3) :
    coordDeriv 0 (modeScalar q w outer) x= -w*modeScalar q w outer x := by
  have hj := mode_reader_static_jet q w hw outer x hr hy
  rw [mode_static_jet q w hw outer (staticPoint x) hr hy] at hj
  have he := congrArg (fun J : ScalarTwoJet (Fin 4) ℂ => J.first 0) hj
  simp [D4BMIngoingFullCurrent.toStatic,staticStreamJet,ofField,staticPoint,angularPoint] at he
  rw [he,modeScalar_value]
  simp [angularPoint,neg_mul,mul_assoc]

/-- Physical stream family in the original ingoing chart. -/
def modeStream (q : XiZeroCopy) (w : ℂ) (outer : Bool) (j : Fin 2) (x : P) : ℂ :=
  physicalLeftModeStream q w outer j (staticPoint x)

/-- The full angular derivatives of the scalar family produce the actual physical reader stream. -/
theorem mode_coexact (q : XiZeroCopy) (w : ℂ) (hw : w.im≠0)
    (outer : Bool) (x : P) (hr : 1<x 1) (hy : 0<x 3) (j : Fin 2) :
    coexactField (modeScalar q w outer) j x=modeStream q w outer j x := by
  have hj := mode_reader_static_jet q w hw outer x hr hy
  rw [mode_static_jet q w hw outer (staticPoint x) hr hy] at hj
  have h2 := congrArg (fun J : ScalarTwoJet (Fin 4) ℂ => J.first 2) hj
  have h3 := congrArg (fun J : ScalarTwoJet (Fin 4) ℂ => J.first 3) hj
  simp [D4BMIngoingFullCurrent.toStatic,staticStreamJet,ofField,staticPoint,angularPoint] at h2 h3
  have h2' : coordDeriv 2 (modeScalar q w outer) x=
    Complex.exp (-w*((staticPoint x) 0:ℂ))*radiusLift (modeProfile q w outer) (x 1)*
      coordDeriv 0 (D4BMLiteralCusp.scalar (physicalAngularParameter q)) (angularPoint x) := by
    simpa [staticPoint,angularPoint,Complex.ofReal_sub,neg_mul] using h2
  have h3' : coordDeriv 3 (modeScalar q w outer) x=
    Complex.exp (-w*((staticPoint x) 0:ℂ))*radiusLift (modeProfile q w outer) (x 1)*
      coordDeriv 1 (D4BMLiteralCusp.scalar (physicalAngularParameter q)) (angularPoint x) := by
    simpa [staticPoint,angularPoint,Complex.ofReal_sub,neg_mul] using h3
  fin_cases j
  · change coordDeriv 3 (modeScalar q w outer) x=_
    rw [h3']
    rfl
  · change -coordDeriv 2 (modeScalar q w outer) x=_
    rw [h2']
    change -(Complex.exp (-w*((staticPoint x) 0:ℂ))*radiusLift (modeProfile q w outer) (x 1)*
      coordDeriv 0 (D4BMLiteralCusp.scalar (physicalAngularParameter q)) (angularPoint x))=
      Complex.exp (-w*((staticPoint x) 0:ℂ))*radiusLift (modeProfile q w outer) (x 1)*
        (-coordDeriv 0 (D4BMLiteralCusp.scalar (physicalAngularParameter q)) (angularPoint x))
    ring

/-- The same original stream is recovered after returning to static coordinates. -/
theorem modeStream_static (q : XiZeroCopy) (w : ℂ) (outer : Bool) (j : Fin 2) :
    (fun z => modeStream q w outer j (D4BMActualIngoingCurrent.ingoingPoint z))=
      physicalLeftModeStream q w outer j := by
  funext z
  have he : staticPoint (D4BMActualIngoingCurrent.ingoingPoint z)=z := by
    ext i
    fin_cases i <;> simp [staticPoint,D4BMActualIngoingCurrent.ingoingPoint]
  change physicalLeftModeStream q w outer j (staticPoint (D4BMActualIngoingCurrent.ingoingPoint z))=_
  rw [he]

private theorem mode_coexact_germ (q : XiZeroCopy) (w : ℂ) (hw : w.im≠0) (outer : Bool)
    (x : P) (hr : 1<x 1) (hy : 0<x 3) (j : Fin 2) :
    coexactField (modeScalar q w outer) j=ᶠ[𝓝 x] modeStream q w outer j := by
  filter_upwards [(isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hr,
    (isOpen_lt continuous_const (continuous_apply 3)).mem_nhds hy] with z hR hY
  exact mode_coexact q w hw outer z hR hY j

/-- The reconstructed physical stream's actual two-jets exist on the entire nonreal frequency family. -/
theorem modeStream_smooth (q : XiZeroCopy) (w : ℂ) (hw : w.im≠0) (outer : Bool)
    (x : P) (hr : 1<x 1) (hy : 0<x 3) (j : Fin 2) :
    ContDiffAt ℝ 2 (modeStream q w outer j) x := by
  have h := modeScalar_smooth q w hw outer x hr hy
  have hc : ContDiffAt ℝ 2 (coexactField (modeScalar q w outer) j) x := by
    fin_cases j
    · exact (coordDeriv_contDiffAt h (by simp) 3).of_le (WithTop.coe_le_coe.mpr le_top)
    · exact ((coordDeriv_contDiffAt h (by simp) 2).of_le (WithTop.coe_le_coe.mpr le_top)).neg
  exact hc.congr_of_eventuallyEq (mode_coexact_germ q w hw outer x hr hy j).symm


private theorem mode_ingoing_smooth (x : P) (hr : 1<x 1) :
    ContDiffAt ℝ ∞ D4BMActualIngoingCurrent.ingoingPoint x := by
  have ht : ContDiffAt ℝ ∞ tortoise (x 1) := by
    have hm : x 1-1≠0 := by linarith
    have hp : x 1+1≠0 := by linarith
    unfold tortoise
    fun_prop
  have htR := ht.comp x (contDiff_apply ℝ ℝ (1:Fin 4)).contDiffAt
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i
  · exact (contDiff_apply ℝ ℝ (0:Fin 4)).contDiffAt.add htR
  · exact (contDiff_apply ℝ ℝ (1:Fin 4)).contDiffAt
  · exact (contDiff_apply ℝ ℝ (2:Fin 4)).contDiffAt
  · exact (contDiff_apply ℝ ℝ (3:Fin 4)).contDiffAt

/-- The complete metric current is attached to the actual original source and
physical reader across the whole nonreal temporal-frequency family. -/
theorem mode_metric_current_eq (q r : XiZeroCopy) (branch : Bool) (amp w : ℂ)
    (hw : w.im≠0) (outer : Bool) (x : D4BMBackground.ExteriorPoint)
    (hp : 0<D4BMActualIngoingCurrent.ingoingPoint x.val 0) :
    D4BMActualIngoingCurrent.metricIngoingCurrent x
      (D4BMActualIngoingCurrent.originalStaticStream q branch amp)
      (physicalLeftModeStream r w outer)=
    D4BMIngoingFullCurrent.current (x.val 1) (x.val 3)
      (fun a => ofField (D4BMActualIngoingCurrent.originalStream q branch amp a)
        (D4BMActualIngoingCurrent.ingoingPoint x.val))
      (fun a => ofField (modeStream r w outer a)
        (D4BMActualIngoingCurrent.ingoingPoint x.val)) := by
  have hP (a : Fin 2) := smooth_two (D4BMOriginalGreenBoundary.originalStream_exterior_smooth q branch amp
    (D4BMActualIngoingCurrent.ingoingPoint x.val) hp x.property.1 x.property.2 a)
  have hQ (a : Fin 2) := modeStream_smooth r w hw outer
    (D4BMActualIngoingCurrent.ingoingPoint x.val) x.property.1 x.property.2 a
  have hs := (mode_ingoing_smooth x.val x.property.1).of_le
    (show (2:ℕ∞ω)≤∞ from WithTop.coe_le_coe.mpr le_top)
  have he : (fun a z => modeStream r w outer a (D4BMActualIngoingCurrent.ingoingPoint z))=
      physicalLeftModeStream r w outer := funext (modeStream_static r w outer)
  have hPs (a : Fin 2) : ContDiffAt ℝ 2
      (D4BMActualIngoingCurrent.originalStaticStream q branch amp a) x.val := (hP a).comp x.val hs
  have hQs (a : Fin 2) : ContDiffAt ℝ 2
      (fun z => modeStream r w outer a (D4BMActualIngoingCurrent.ingoingPoint z)) x.val := (hQ a).comp x.val hs
  rw [← he,D4BMActualIngoingCurrent.metricIngoingCurrent_eq _ _ x hPs hQs]
  change D4BMPhysicalLiftCurrent.ingoingAction x
    (fun a => ofField (fun z => D4BMActualIngoingCurrent.originalStream q branch amp a
      (D4BMActualIngoingCurrent.ingoingPoint z)) x.val) _=_
  simp_rw [D4BMActualIngoingCurrent.ofField_ingoing_comp x.property.1 (hP _),
    D4BMActualIngoingCurrent.ofField_ingoing_comp x.property.1 (hQ _)]
  exact D4BMIngoingFullCurrent.original_ingoing_current x _ _

/-- The actual reconstructed metric density with its physical temporal reader left independent. -/
def modeMetricDensity (q r : XiZeroCopy) (branch outer : Bool) (amp w : ℂ) (j : Fin 2) (x : P) : ℂ :=
  let z := staticPoint x
  let U := D4BMActualIngoingCurrent.originalStaticStream q branch amp
  let W := physicalLeftModeStream r w outer
  let J := fun k => (x 1:ℂ)^(2 : ℕ)/(x 3:ℂ)^(2 : ℕ)*D4BMMixedActionCurrent.actionSymplectic
    (D4BMBackground.jet (x 1) (x 3))
    (ofMetricField (D4BMActualIngoingCurrent.reconstructedMetric U) z)
    (ofMetricField (D4BMActualIngoingCurrent.reconstructedMetric W) z) k
  if j=0 then J 0+J 1/((x 1:ℂ)^(2 : ℕ)-1) else J 1

/-- The family recovers the original prescribed-QNM metric density exactly. -/
theorem modeMetricDensity_specialize (q r : XiZeroCopy) (branch side outer : Bool) (amp : ℂ) :
    modeMetricDensity q r branch outer amp (frequency r side)=
      D4BMOriginalOrbitCurrent.metricDensity q r branch side outer amp := rfl

private theorem mode_metric_stream (q r : XiZeroCopy) (branch outer : Bool) (amp w : ℂ)
    (hw : w.im≠0) (x : P) (hp : 0<x 0) (hr : 1<x 1) (hy : 0<x 3) (j : Fin 2) :
    modeMetricDensity q r branch outer amp w j x=
      D4BMIngoingFullCurrent.current (x 1) (x 3)
        (fun a => ofField (coexactField (sourceScalar q branch amp) a) x)
        (fun a => ofField (coexactField (modeScalar r w outer) a) x) (if j=0 then 0 else 1) := by
  let z : D4BMBackground.ExteriorPoint := ⟨staticPoint x,hr,hy⟩
  have hz : D4BMActualIngoingCurrent.ingoingPoint z.val=x := by
    ext i
    fin_cases i <;> simp [z,staticPoint,D4BMActualIngoingCurrent.ingoingPoint]
  have hpz : 0<D4BMActualIngoingCurrent.ingoingPoint z.val 0 := by rw [hz];exact hp
  have he := mode_metric_current_eq q r branch amp w hw outer z hpz
  rw [hz] at he
  have hS := D4BMOriginalGreenBoundary.originalPotential_exterior_smooth q branch amp x hp hr hy
  have hSJ (a : Fin 2) : ofField (coexactField (sourceScalar q branch amp) a) x=
      ofField (D4BMActualIngoingCurrent.originalStream q branch amp a) x := by
    apply ofField_germ
    filter_upwards [(hS.of_le (show (2:ℕ∞ω)≤∞ from WithTop.coe_le_coe.mpr le_top)).eventually (by norm_num)] with y hys
    exact source_coexact q branch amp y (hys.differentiableAt (by norm_num)) a
  have hWJ (a : Fin 2) : ofField (coexactField (modeScalar r w outer) a) x=
      ofField (modeStream r w outer a) x := ofField_germ (mode_coexact_germ r w hw outer x hr hy a)
  simp_rw [hSJ,hWJ]
  have h := congrArg (fun v : Fin 4 → ℂ => v (if j=0 then 0 else 1)) he
  calc
    _ = D4BMActualIngoingCurrent.metricIngoingCurrent z
        (D4BMActualIngoingCurrent.originalStaticStream q branch amp)
        (physicalLeftModeStream r w outer) (if j=0 then 0 else 1) := by fin_cases j <;> rfl
    _ = _ := h

/-- The full original metric-family density has its actual scalar reduction,
with the original forcing retained and without assuming temporal matching. -/
theorem mode_metric_density (q r : XiZeroCopy) (branch outer : Bool) (amp w : ℂ)
    (hw : w.im≠0) (x : P) (hp : 0<x 0) (hr : 1<x 1) (hy : 0<x 3) (j : Fin 2) :
    modeMetricDensity q r branch outer amp w j x=
      1/(x 1:ℂ)^(2 : ℕ)*(D4BMOriginalOrbitCurrent.pairing
        (D4BMOriginalOrbitCurrent.orbitDerivative (sourceScalar q branch amp) j)
        (scalarContact (modeScalar r w outer)) x-
      D4BMOriginalOrbitCurrent.pairing (D4BMOriginalOrbitCurrent.forcedContact q branch amp)
        (D4BMOriginalOrbitCurrent.orbitDerivative (modeScalar r w outer) j) x) := by
  rw [mode_metric_stream q r branch outer amp w hw x hp hr hy j,
    D4BMOriginalOrbitCurrent.coexact_orbit_current
      (D4BMOriginalGreenBoundary.sourceScalar_exterior_smooth q branch amp x hp hr hy)
      (modeScalar_smooth r w hw outer x hr hy) j]
  have hg : scalarContact (sourceScalar q branch amp)=ᶠ[𝓝 x]
      D4BMOriginalOrbitCurrent.forcedContact q branch amp := by
    filter_upwards [(isOpen_lt continuous_const (continuous_apply 0)).mem_nhds hp,
      (isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hr,
      (isOpen_lt continuous_const (continuous_apply 3)).mem_nhds hy] with z hP hR hY
    exact D4BMOriginalSourceContact.original_scalar_contact q branch amp z hP hR hY
  have hc (a : Fin 2) : coexactField (scalarContact (sourceScalar q branch amp)) a x=
      coexactField (D4BMOriginalOrbitCurrent.forcedContact q branch amp) a x := by
    have hd (i : Fin 4) := congrArg (fun L => L (Pi.single i 1)) (hg.fderiv_eq (𝕜:=ℝ))
    fin_cases a
    · exact hd 3
    · exact congrArg Neg.neg (hd 2)
  simp only [D4BMOriginalOrbitCurrent.pairing,hc,Fin.sum_univ_two]
  ring

private theorem mode_angular_germ (q : XiZeroCopy) (w : ℂ) (hw : w.im≠0) (outer : Bool) (x : P)
    (hr : 1<x 1) (hy : 0<x 3) :
    angularLap (modeScalar q w outer) =ᶠ[𝓝 x] fun z => eigenvalue q*modeScalar q w outer z := by
  filter_upwards [(isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hr,
    (isOpen_lt continuous_const (continuous_apply 3)).mem_nhds hy] with z hR hY
  exact mode_angular_equation q w hw outer z hR hY

private theorem mode_partial_angular (q : XiZeroCopy) (w : ℂ) (hw : w.im≠0) (outer : Bool) (x : P)
    (hr : 1<x 1) (hy : 0<x 3) (i : Fin 4) (hi : i≠3) :
    angularLap (coordDeriv i (modeScalar q w outer)) x=
      eigenvalue q*coordDeriv i (modeScalar q w outer) x := by
  have hs := modeScalar_smooth q w hw outer x hr hy
  have he := (mode_angular_germ q w hw outer x hr hy).fderiv_eq (𝕜 := ℝ)
  have hd := congrArg (fun L : P →L[ℝ] ℂ => L (Pi.single i 1)) he
  change coordDeriv i (angularLap (modeScalar q w outer)) x=
    coordDeriv i (fun z => eigenvalue q*modeScalar q w outer z) x at hd
  rw [angularLap_partial hs i hi,coordDeriv_mul (differentiableAt_const (eigenvalue q))
    (hs.differentiableAt (by simp))] at hd
  simpa [coordDeriv] using hd

/-- Both reader factors in the physical temporal/radial currents have the same angular eigenvalue. -/
theorem mode_orbit_angular (q : XiZeroCopy) (w : ℂ) (hw : w.im≠0) (outer : Bool) (x : P)
    (hr : 1<x 1) (hy : 0<x 3) (j : Fin 2) :
    angularLap (D4BMOriginalOrbitCurrent.orbitDerivative (modeScalar q w outer) j) x=
      eigenvalue q*D4BMOriginalOrbitCurrent.orbitDerivative (modeScalar q w outer) j x := by
  have hs := modeScalar_smooth q w hw outer x hr hy
  have h0 := smooth_two (smooth_partial hs 0)
  have h1 := smooth_two (smooth_partial hs 1)
  have hR : ContDiffAt ℝ 2 (fun R : ℝ => (R:ℂ)^(2 : ℕ)-1) (x 1) :=
    (Complex.ofRealCLM.contDiff.contDiffAt.pow 2).sub contDiffAt_const
  by_cases hj : j=0
  · subst j
    exact mode_partial_angular q w hw outer x hr hy 1 (by decide)
  · have hfun : D4BMOriginalOrbitCurrent.orbitDerivative (modeScalar q w outer) j=
        fun z => ((z 1:ℂ)^(2 : ℕ)-1)*coordDeriv 1 (modeScalar q w outer) z+coordDeriv 0 (modeScalar q w outer) z := by
      funext z
      exact if_neg hj
    rw [hfun]
    change angularLap (fun z => ((z 1:ℂ)^(2 : ℕ)-1)*coordDeriv 1 (modeScalar q w outer) z+
      coordDeriv 0 (modeScalar q w outer) z) x=_
    have hR' : ContDiffAt ℝ 2 (fun z : P => ((z 1:ℂ)^(2 : ℕ)-1)*coordDeriv 1 (modeScalar q w outer) z) x := by
      simpa only [Function.comp_def] using (hR.comp x (contDiff_apply ℝ ℝ (1:Fin 4)).contDiffAt).mul h1
    rw [angularLap_add hR' h0,
      angularLap_radial_mul _ hR h1,mode_partial_angular q w hw outer x hr hy 1 (by decide),
      mode_partial_angular q w hw outer x hr hy 0 (by decide)]
    change _=eigenvalue q*(((x 1:ℂ)^(2 : ℕ)-1)*coordDeriv 1 (modeScalar q w outer) x+
      coordDeriv 0 (modeScalar q w outer) x)
    ring

/-- The actual reader contact remains in the same angular eigenspace. -/
theorem mode_contact_angular (q : XiZeroCopy) (w : ℂ) (hw : w.im≠0) (outer : Bool) (x : P)
    (hr : 1<x 1) (hy : 0<x 3) :
    angularLap (scalarContact (modeScalar q w outer)) x=
      eigenvalue q*(eigenvalue q-2)*modeScalar q w outer x := by
  have hg : scalarContact (modeScalar q w outer) =ᶠ[𝓝 x]
      fun z => (eigenvalue q-2)*modeScalar q w outer z := by
    filter_upwards [(isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hr,
      (isOpen_lt continuous_const (continuous_apply 3)).mem_nhds hy] with z hR hY
    exact mode_scalar_contact q w hw outer z hR hY
  have hj := ofField_germ hg
  have he := congrArg (fun J : ScalarTwoJet (Fin 4) ℂ => (x 3:ℂ)^(2 : ℕ)*(J.second 2 2+J.second 3 3)) hj
  change angularLap (scalarContact (modeScalar q w outer)) x=
    angularLap (fun z => (eigenvalue q-2)*modeScalar q w outer z) x at he
  rw [he,angularLap_const_mul _ (smooth_two (modeScalar_smooth q w hw outer x hr hy)),
    mode_angular_equation q w hw outer x hr hy]
  ring

end
end RHTower.D4BMOriginalReaderEquation
