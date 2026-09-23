import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalReaderEquation
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMModularCoexact
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhysicalCoreCutoff
import GaloisForLFunctions.RHTower.SelbergMaassTraceBoundary

/-!
# Original metric transfers on the modular domain

The genuine temporal/radial derivatives and contacts preserve modular
invariance on the physical exterior. Their paired side and curved-core
normal fluxes cancel on each finite modular domain. The actual metric
pairing therefore retains only its original cusp-top angular flux.
All original time, radius and height cutoffs remain finite in this identity.
-/

open Set Filter Topology MeasureTheory UpperHalfPlane ModularGroup
open scoped ContDiff MatrixGroups
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal
attribute [-instance] RCLike.innerProductSpace
namespace RHTower.D4BMOriginalModularOrbit
open GaloisForLFunctions.HTGeometry ScalarTwoJet
open D4BMOriginalAngularCurrent D4BMOriginalSourceContact D4BMOriginalOrbitCurrent
open D4BMMetricReconstruction D4BMModularCore D4BMJointSource D4BMHorizon D4BMGlobalAngularResponse
noncomputable section
private abbrev P := Fin 4 → ℝ
private abbrev F := P → ℂ
private def ExteriorSmooth (U : F) : Prop :=
  ∀ x, 0<x 0 → 1<x 1 → 0<x 3 → ContDiffAt ℝ ∞ U x
private def ExteriorModular (U : F) : Prop :=
  ∀ p R, 0<p → 1<R → ∀ (A : SL(2,ℤ)) (z : UpperHalfPlane),
    U (slice p R ((A • z:UpperHalfPlane):ℂ))=U (slice p R z)
private def freezeAngular (z : ℂ) (x : P) : P := ![x 0,x 1,z.re,z.im]
private def freezeLinear : P →L[ℝ] P :=
  ContinuousLinearMap.pi ![ContinuousLinearMap.proj 0,ContinuousLinearMap.proj 1,0,0]
private theorem freeze_deriv (z : ℂ) (x : P) :
    HasFDerivAt (freezeAngular z) freezeLinear x := by
  convert! freezeLinear.hasFDerivAt.add_const (![0,0,z.re,z.im] : P) using 1
  funext y i
  fin_cases i <;> simp [freezeAngular,freezeLinear]
private theorem freeze_partial {U : F} (z : ℂ) (x : P)
    (hU : DifferentiableAt ℝ U (freezeAngular z x)) (i : Fin 4) (hi : i=0 ∨ i=1) :
    coordDeriv i (U ∘ freezeAngular z) x=coordDeriv i U (freezeAngular z x) := by
  unfold coordDeriv
  rw [(hU.hasFDerivAt.comp x (freeze_deriv z x)).fderiv,ContinuousLinearMap.comp_apply]
  have hv : freezeLinear (Pi.single i 1)=Pi.single i 1 := by
    rcases hi with rfl | rfl <;> ext k <;> fin_cases k <;> simp [freezeLinear]
  rw [hv]
private theorem smooth_partial {U : F} (hU : ExteriorSmooth U) (i : Fin 4) :
    ExteriorSmooth (coordDeriv i U) := by
  intro x hp hr hy
  exact coordDeriv_contDiffAt (hU x hp hr hy) (by simp) i
private theorem modular_partial {U : F} (hU : ExteriorSmooth U) (hm : ExteriorModular U)
    (i : Fin 4) (hi : i=0 ∨ i=1) : ExteriorModular (coordDeriv i U) := by
  intro p R hp hr A z
  let x : P := ![p,R,0,1]
  have he : U ∘ freezeAngular ((A • z:UpperHalfPlane):ℂ) =ᶠ[𝓝 x] U ∘ freezeAngular (z:ℂ) := by
    filter_upwards [(isOpen_lt continuous_const (continuous_apply 0)).mem_nhds hp,
      (isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hr] with y hy0 hy1
    exact hm (y 0) (y 1) hy0 hy1 A z
  have hd := congrArg (fun L : P →L[ℝ] ℂ => L (Pi.single i 1)) (he.fderiv_eq (𝕜 := ℝ))
  change coordDeriv i (U ∘ freezeAngular ((A • z:UpperHalfPlane):ℂ)) x=coordDeriv i (U ∘ freezeAngular (z:ℂ)) x at hd
  rw [freeze_partial _ _ ((hU _ hp hr (A • z).im_pos).differentiableAt (by simp)) i hi,
    freeze_partial _ _ ((hU _ hp hr z.im_pos).differentiableAt (by simp)) i hi] at hd
  exact hd
private theorem orbit_smooth {U : F} (hU : ExteriorSmooth U) (j : Fin 2) :
    ExteriorSmooth (orbitDerivative U j) := by
  intro x hp hr hy
  have h0 := smooth_partial hU 0 x hp hr hy
  have h1 := smooth_partial hU 1 x hp hr hy
  have hR : ContDiffAt ℝ ∞ (fun z : P => (z 1:ℂ)) x :=
    (Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ (1:Fin 4))).contDiffAt
  by_cases hj : j=0
  · subst j
    exact h1
  · have he : orbitDerivative U j=(fun z => ((z 1:ℂ)^(2 : ℕ)-1)*coordDeriv 1 U z+coordDeriv 0 U z) := by
      funext z
      exact if_neg hj
    rw [he]
    exact ((hR.pow 2).sub contDiffAt_const).mul h1 |>.add h0
private theorem orbit_modular {U : F} (hU : ExteriorSmooth U) (hm : ExteriorModular U) (j : Fin 2) :
    ExteriorModular (orbitDerivative U j) := by
  intro p R hp hr A z
  have h0 := modular_partial hU hm 0 (Or.inl rfl) p R hp hr A z
  have h1 := modular_partial hU hm 1 (Or.inr rfl) p R hp hr A z
  simp only [orbitDerivative,slice,Matrix.cons_val_one,Matrix.cons_val_zero] at h0 h1 ⊢
  rw [h0,h1]
private theorem contact_smooth {U : F} (hU : ExteriorSmooth U) : ExteriorSmooth (scalarContact U) := by
  intro x hp hr hy
  have h0 := smooth_partial hU 0 x hp hr hy
  have h1 := smooth_partial hU 1 x hp hr hy
  have h01 := smooth_partial (smooth_partial hU 1) 0 x hp hr hy
  have h10 := smooth_partial (smooth_partial hU 0) 1 x hp hr hy
  have h11 := smooth_partial (smooth_partial hU 1) 1 x hp hr hy
  have hR : ContDiffAt ℝ ∞ (fun z : P => (z 1:ℂ)) x :=
    (Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ (1:Fin 4))).contDiffAt
  change ContDiffAt ℝ ∞ (fun z : P =>
    -(z 1:ℂ)^(2 : ℕ)*((z 1:ℂ)^(2 : ℕ)-1)*coordDeriv 1 (coordDeriv 1 U) z-
    (z 1:ℂ)^(2 : ℕ)*(coordDeriv 0 (coordDeriv 1 U) z+coordDeriv 1 (coordDeriv 0 U) z)-
    2*(z 1:ℂ)*coordDeriv 1 U z+2*(z 1:ℂ)*coordDeriv 0 U z) x
  exact ((((hR.pow 2).neg.mul ((hR.pow 2).sub contDiffAt_const)).mul h11).sub
    ((hR.pow 2).mul (h01.add h10)) |>.sub ((contDiffAt_const.mul hR).mul h1)).add
      ((contDiffAt_const.mul hR).mul h0)
private theorem contact_modular {U : F} (hU : ExteriorSmooth U) (hm : ExteriorModular U) :
    ExteriorModular (scalarContact U) := by
  intro p R hp hr A z
  have h0 := modular_partial hU hm 0 (Or.inl rfl) p R hp hr A z
  have h1 := modular_partial hU hm 1 (Or.inr rfl) p R hp hr A z
  have h01 := modular_partial (smooth_partial hU 1) (modular_partial hU hm 1 (Or.inr rfl)) 0 (Or.inl rfl) p R hp hr A z
  have h10 := modular_partial (smooth_partial hU 0) (modular_partial hU hm 0 (Or.inl rfl)) 1 (Or.inr rfl) p R hp hr A z
  have h11 := modular_partial (smooth_partial hU 1) (modular_partial hU hm 1 (Or.inr rfl)) 1 (Or.inr rfl) p R hp hr A z
  change -(R:ℂ)^(2 : ℕ)*((R:ℂ)^(2 : ℕ)-1)*coordDeriv 1 (coordDeriv 1 U) (slice p R ((A • z:UpperHalfPlane):ℂ))-
    (R:ℂ)^(2 : ℕ)*(coordDeriv 0 (coordDeriv 1 U) (slice p R ((A • z:UpperHalfPlane):ℂ))+coordDeriv 1 (coordDeriv 0 U) (slice p R ((A • z:UpperHalfPlane):ℂ)))-
    2*(R:ℂ)*coordDeriv 1 U (slice p R ((A • z:UpperHalfPlane):ℂ))+2*(R:ℂ)*coordDeriv 0 U (slice p R ((A • z:UpperHalfPlane):ℂ))=_
  rw [h0,h1,h01,h10,h11]
  rfl
private theorem source_smooth (q : XiZeroCopy) (branch : Bool) (amp : ℂ) :
    ExteriorSmooth (sourceScalar q branch amp) :=
  D4BMOriginalGreenBoundary.sourceScalar_exterior_smooth q branch amp
private theorem source_modular (q : XiZeroCopy) (branch : Bool) (amp : ℂ) :
    ExteriorModular (sourceScalar q branch amp) := by
  intro p R hp hr A z
  change (R:ℂ)*D4BMOriginalCausalPotential.originalPotential q branch amp p
    (p-2*D4BMIngoingCoordinates.tortoise R) (A • z).re (Real.log (A • z).im)=_
  rw [D4BMOriginalCausalPotential.originalPotential_modular]
  rfl
private theorem reader_smooth (q : XiZeroCopy) (side outer : Bool) :
    ExteriorSmooth (leftScalar q side outer) := by
  intro x hp hr hy
  exact leftScalar_smooth q side outer x hr hy
private theorem reader_modular (q : XiZeroCopy) (side outer : Bool) :
    ExteriorModular (leftScalar q side outer) := by
  intro p R hp hr A z
  rw [leftScalar_value,leftScalar_value]
  have h := physicalScalar_modular q A z
  change D4BMLiteralCusp.scalar (physicalAngularParameter q) (angularPoint (slice p R ((A • z:UpperHalfPlane):ℂ)))=
    D4BMLiteralCusp.scalar (physicalAngularParameter q) (angularPoint (slice p R z)) at h
  simp only [slice,Matrix.cons_val_zero,Matrix.cons_val_one] at h ⊢
  rw [h]

private def planarField (U : F) (p R : ℝ) (z : Fin 2 → ℝ) : ℂ := U ![p,R,z 0,z 1]
private def planarEmbedding : (Fin 2 → ℝ) →L[ℝ] P :=
  ContinuousLinearMap.pi ![0,0,ContinuousLinearMap.proj 0,ContinuousLinearMap.proj 1]
private theorem planar_deriv (p R : ℝ) (z : Fin 2 → ℝ) :
    HasFDerivAt (fun w : Fin 2 → ℝ => (![p,R,w 0,w 1] : P)) planarEmbedding z := by
  convert! planarEmbedding.hasFDerivAt.add_const (![p,R,0,0] : P) using 1
  funext w i
  fin_cases i <;> simp [planarEmbedding]
private theorem planar_partial (U : F) (p R : ℝ) (z : Fin 2 → ℝ)
    (hU : DifferentiableAt ℝ U ![p,R,z 0,z 1]) (j : Fin 2) :
    coordDeriv j (planarField U p R) z=coordDeriv (angularIndex j) U ![p,R,z 0,z 1] := by
  unfold coordDeriv planarField
  have he := (hU.hasFDerivAt.comp z (planar_deriv p R z)).fderiv
  simp only [Function.comp_def] at he
  rw [he,ContinuousLinearMap.comp_apply]
  have hv : planarEmbedding (Pi.single j 1)=Pi.single (angularIndex j) 1 := by
    fin_cases j <;> ext i <;> fin_cases i <;> simp [planarEmbedding,angularIndex]
  rw [hv]
private theorem planar_smooth (U : F) (p R : ℝ) (hp : 0<p) (hr : 1<R)
    (hU : ExteriorSmooth U) (z : Fin 2 → ℝ) (hy : 0<z 1) :
    ContDiffAt ℝ ∞ (planarField U p R) z := by
  have hm : ContDiff ℝ ∞ (fun w : Fin 2 → ℝ => (![p,R,w 0,w 1] : P)) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i <;> first | exact contDiff_const | exact contDiff_apply ℝ ℝ _
  exact (hU _ hp hr hy).comp z hm.contDiffAt
private def normalCurrent (U V : F) (p R : ℝ) (z a : ℂ) : ℂ :=
  (a.re:ℂ)*transfer U V 0 (slice p R z)+(a.im:ℂ)*transfer U V 1 (slice p R z)
private theorem normalCurrent_coexact (U V : F) (p R : ℝ) (hp : 0<p) (hr : 1<R)
    (hV : ExteriorSmooth V) (z : UpperHalfPlane) (a : ℂ) :
    normalCurrent U V p R z a=U (slice p R z)*
      covectorAction (coexact (planarField V p R)) (coordinates z) (-Complex.I*a) := by
  have hd (j : Fin 2) := planar_partial V p R (coordinates z)
    ((hV _ hp hr z.im_pos).differentiableAt (by simp)) j
  unfold normalCurrent transfer covectorAction coexact
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,hd]
  simp [Complex.mul_re,Complex.mul_im,coordinates,slice,angularIndex]
  ring
private theorem normalCurrent_modular (U V : F) (p R : ℝ) (hp : 0<p) (hr : 1<R)
    (hU : ExteriorModular U) (hV : ExteriorSmooth V) (hmV : ExteriorModular V)
    (A : SL(2,ℤ)) (z : UpperHalfPlane) (a : ℂ) :
    normalCurrent U V p R z a=normalCurrent U V p R ((A • z:UpperHalfPlane):ℂ) ((1/(denom A z)^(2 : ℕ))*a) := by
  rw [normalCurrent_coexact U V p R hp hr hV,normalCurrent_coexact U V p R hp hr hV,
    hU p R hp hr A z]
  have he := coexact_modular_action A (planarField V p R)
    (planar_smooth V p R hp hr hV) (hmV p R hp hr A) z (-Complex.I*a)
  have hv : -Complex.I*((1/(denom A z)^(2 : ℕ))*a)=(1/(denom A z)^(2 : ℕ))*(-Complex.I*a) := by ring
  rw [hv,he]
private theorem normalCurrent_inversion (U V : F) (p R : ℝ) (hp : 0<p) (hr : 1<R)
    (hU : ExteriorModular U) (hV : ExteriorSmooth V) (hmV : ExteriorModular V)
    (z : UpperHalfPlane) :
    normalCurrent U V p R z z+normalCurrent U V p R ((S • z:UpperHalfPlane):ℂ) ((S • z:UpperHalfPlane):ℂ)=0 := by
  have h := normalCurrent_modular U V p R hp hr hU hV hmV S z z
  have hv : (1/(denom S z)^(2 : ℕ))*(z:ℂ)=-((S • z:UpperHalfPlane):ℂ) := by
    simp only [UpperHalfPlane.modular_S_smul]
    simp [denom,ModularGroup.S,inv_neg]
    field_simp
  rw [hv] at h
  have hn : normalCurrent U V p R ((S • z:UpperHalfPlane):ℂ) (-((S • z:UpperHalfPlane):ℂ))=
      -normalCurrent U V p R ((S • z:UpperHalfPlane):ℂ) ((S • z:UpperHalfPlane):ℂ) := by
    simp only [normalCurrent,Complex.neg_re,Complex.neg_im,Complex.ofReal_neg]
    ring
  rw [hn] at h
  rw [h]
  ring

open GaloisForLFunctions.RHTower SelbergMaassMean SelbergMaassTraceStokes SelbergModularDomainSlices
private theorem side_cancellation (U V : F) (p R : ℝ) (hp : 0<p) (hr : 1<R)
    (hU : ExteriorModular U) (hV : ExteriorSmooth V) (hmV : ExteriorModular V)
    {y : ℝ} (hy : 0<y) :
    transfer U V 0 (slice p R (point (1/2) y))=transfer U V 0 (slice p R (point (-(1/2)) y)) := by
  have h := normalCurrent_modular U V p R hp hr hU hV hmV T (ofComplex (point (-(1/2)) y)) 1
  rw [SelbergMaassTraceBoundary.translation_point _ hy,show -(1/2:ℝ)+1=1/2 by ring] at h
  have hz (x : ℝ) : 0<(point x y).im := by simpa [point] using hy
  rw [ofComplex_apply_of_im_pos (hz (1/2)),ofComplex_apply_of_im_pos (hz (-(1/2)))] at h
  simpa [normalCurrent,denom,ModularGroup.T] using h.symm

private theorem arc_cancellation (U V : F) (p R : ℝ) (hp : 0<p) (hr : 1<R)
    (hU : ExteriorModular U) (hV : ExteriorSmooth V) (hmV : ExteriorModular V)
    {x y : ℝ} (hy : 0<y) (hxy : x^(2 : ℕ)+y^(2 : ℕ)=1) :
    ((-x/y:ℝ):ℂ)*transfer U V 0 (slice p R (point x y))-transfer U V 1 (slice p R (point x y))+
    ((x/y:ℝ):ℂ)*transfer U V 0 (slice p R (point (-x) y))-transfer U V 1 (slice p R (point (-x) y))=0 := by
  have h := normalCurrent_inversion U V p R hp hr hU hV hmV (ofComplex (point x y))
  rw [SelbergMaassTraceBoundary.inversion_on_unit_circle hy hxy] at h
  have hz (t : ℝ) : 0<(point t y).im := by simpa [point] using hy
  rw [ofComplex_apply_of_im_pos (hz x),ofComplex_apply_of_im_pos (hz (-x))] at h
  have hRe (a b : ℝ) : (point a b).re=a := by simp [point]
  have hIm (a b : ℝ) : (point a b).im=b := by simp [point]
  simp only [normalCurrent,hRe,hIm,Complex.ofReal_neg] at h
  simp only [Complex.ofReal_div,Complex.ofReal_neg]
  field_simp [Complex.ofReal_ne_zero.mpr hy.ne']
  linear_combination -h

/-- The original top angular normal flux for an arbitrary pair of spacetime fields. -/
def topFlux (U V : F) (p R Y : ℝ) : ℂ :=
  ∫ x in (-(1/2:ℝ))..1/2, transfer U V 1 (slice p R (point x Y))
private theorem boundary_eq_top (U V : F) (p R : ℝ) (hp : 0<p) (hr : 1<R)
    (hU : ExteriorModular U) (hV : ExteriorSmooth V) (hmV : ExteriorModular V)
    {Y : ℝ} (hY : 1≤Y) :
    boundary (transfer U V 0) (transfer U V 1) p R Y=topFlux U V p R Y := by
  have hfloor : arcFloor≤Y := (arcHeight_le_one ⟨by norm_num,le_rfl⟩).trans hY
  have hs : (∫ y in arcFloor..Y, transfer U V 0 (slice p R (point (1/2) y))-
      transfer U V 0 (slice p R (point (-(1/2)) y)))=0 := by
    calc
      _ = ∫ y in arcFloor..Y, (0:ℂ) := by
        apply intervalIntegral.integral_congr
        intro y hy
        have hyI : y ∈ Icc arcFloor Y := by simpa only [uIcc_of_le hfloor] using hy
        change transfer U V 0 (slice p R (point (1/2) y))-transfer U V 0 (slice p R (point (-(1/2)) y))=0
        rw [side_cancellation U V p R hp hr hU hV hmV (arcFloor_pos.trans_le hyI.1),sub_self]
      _ = 0 := by simp
  have ha : (∫ x in (0:ℝ)..1/2,
      ((-x/arcHeight x:ℝ):ℂ)*transfer U V 0 (slice p R (point x (arcHeight x)))-transfer U V 1 (slice p R (point x (arcHeight x)))+
      ((x/arcHeight x:ℝ):ℂ)*transfer U V 0 (slice p R (point (-x) (arcHeight x)))-transfer U V 1 (slice p R (point (-x) (arcHeight x))))=0 := by
    calc
      _ = ∫ x in (0:ℝ)..1/2, (0:ℂ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        have hxI : x ∈ Icc (0:ℝ) (1/2) := by simpa using hx
        have hc : x ∈ Icc (-(1/2:ℝ)) (1/2) := ⟨by linarith [hxI.1],hxI.2⟩
        exact arc_cancellation U V p R hp hr hU hV hmV (arcHeight_pos hc) (by
          rw [arcHeight_sq hc];ring)
      _ = 0 := by simp
  simp only [boundary,hs,ha,zero_add,add_zero,topFlux]

private theorem forced_modular (q : XiZeroCopy) (branch : Bool) (amp : ℂ) :
    ExteriorModular (forcedContact q branch amp) := by
  intro p R hp hr A z
  have hA := original_scalar_contact q branch amp (slice p R ((A • z:UpperHalfPlane):ℂ)) hp hr (A • z).im_pos
  have hz := original_scalar_contact q branch amp (slice p R (z:ℂ)) hp hr z.im_pos
  change scalarContact (sourceScalar q branch amp) (slice p R ((A • z:UpperHalfPlane):ℂ))=
    forcedContact q branch amp (slice p R ((A • z:UpperHalfPlane):ℂ)) at hA
  change scalarContact (sourceScalar q branch amp) (slice p R (z:ℂ))=
    forcedContact q branch amp (slice p R (z:ℂ)) at hz
  rw [← hA,← hz]
  exact contact_modular (source_smooth q branch amp) (source_modular q branch amp) p R hp hr A z

/-- Both complete original metric transfers have exactly their top angular flux:
the paired vertical sides and curved modular core cancel at finite time and radius. -/
theorem original_transfer_boundary (q r : XiZeroCopy) (branch side outer : Bool) (amp : ℂ)
    (p R : ℝ) (hp : 0<p) (hr : 1<R) {Y : ℝ} (hY : 1≤Y) (j : Fin 2) :
    let U := sourceScalar q branch amp
    let W := leftScalar r side outer
    let A := orbitDerivative U j
    let D := forcedContact q branch amp
    let E := orbitDerivative W j
    boundary (transfer A (scalarContact W) 0) (transfer A (scalarContact W) 1) p R Y=
      topFlux A (scalarContact W) p R Y ∧
    boundary (transfer D E 0) (transfer D E 1) p R Y=topFlux D E p R Y := by
  dsimp only
  constructor
  · exact boundary_eq_top _ _ p R hp hr
      (orbit_modular (source_smooth q branch amp) (source_modular q branch amp) j)
      (contact_smooth (reader_smooth r side outer))
      (contact_modular (reader_smooth r side outer) (reader_modular r side outer)) hY
  · exact boundary_eq_top _ _ p R hp hr (forced_modular q branch amp)
      (orbit_smooth (reader_smooth r side outer) j)
      (orbit_modular (reader_smooth r side outer) (reader_modular r side outer) j) hY

/-- The actual temporal/radial metric pairing, with its complete original forcing,
reduces to scalar periods and only the original cusp-top normal flux. -/
theorem original_metric_top_integral (q r : XiZeroCopy) (branch side outer : Bool) (amp : ℂ)
    (p R : ℝ) (hp : 0<p) (hr : 1<R) {Y : ℝ} (hY : 1≤Y) (j : Fin 2) :
    let U := sourceScalar q branch amp
    let W := leftScalar r side outer
    let A := orbitDerivative U j
    let D := forcedContact q branch amp
    let E := orbitDerivative W j
    (∫ w in domain Y, metricDensity q r branch side outer amp j (slice p R (point w.1 w.2)))+
      1/(R:ℂ)^(2 : ℕ)*((D4BMLeftModeRadialEquation.eigenvalue r*(D4BMLeftModeRadialEquation.eigenvalue r-2))*
        D4BMOriginalReaderEquation.scalarPeriod A W p R Y-
        D4BMLeftModeRadialEquation.eigenvalue r*D4BMOriginalReaderEquation.scalarPeriod D E p R Y)=
      1/(R:ℂ)^(2 : ℕ)*(topFlux A (scalarContact W) p R Y-topFlux D E p R Y) := by
  dsimp only
  have h := D4BMOriginalReaderEquation.original_metric_scalar_integral q r branch side outer amp p R hp hr hY j
  have hb := original_transfer_boundary q r branch side outer amp p R hp hr hY j
  dsimp only at h hb
  rw [hb.1,hb.2] at h
  exact h


open D4BMOriginalReaderEquation D4BMLeftModeRadialEquation

private theorem lap_smooth {U : F} (hU : ExteriorSmooth U) :
    ExteriorSmooth (angularLap U) := by
  intro x hp hr hy
  have hY : ContDiffAt ℝ ∞ (fun z : P => (z 3:ℂ)) x :=
    (Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ (3:Fin 4))).contDiffAt
  exact (hY.pow 2).mul ((smooth_partial (smooth_partial hU 2) 2 x hp hr hy).add
    (smooth_partial (smooth_partial hU 3) 3 x hp hr hy))

private theorem forced_smooth (q : XiZeroCopy) (branch : Bool) (amp : ℂ) :
    ExteriorSmooth (forcedContact q branch amp) := by
  intro x hp hr hy
  have he : scalarContact (sourceScalar q branch amp) =ᶠ[𝓝 x] forcedContact q branch amp := by
    filter_upwards [(isOpen_lt continuous_const (continuous_apply 0)).mem_nhds hp,
      (isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hr,
      (isOpen_lt continuous_const (continuous_apply 3)).mem_nhds hy] with z hz0 hz1 hz3
    exact original_scalar_contact q branch amp z hz0 hz1 hz3
  exact (contact_smooth (source_smooth q branch amp) x hp hr hy).congr_of_eventuallyEq he.symm

private theorem period_integrable (U V : F) (p R Y : ℝ) (hp : 0<p) (hr : 1<R)
    (hU : ExteriorSmooth U) (hV : ExteriorSmooth V) :
    IntegrableOn (fun w : ℝ×ℝ =>
      U (slice p R (point w.1 w.2))*V (slice p R (point w.1 w.2))/(w.2:ℂ)^(2 : ℕ)) (domain Y) := by
  have hm : Continuous (fun w : ℝ×ℝ => slice p R (point w.1 w.2)) := by
    unfold slice point
    fun_prop
  have hc : ContinuousOn (fun w : ℝ×ℝ =>
      U (slice p R (point w.1 w.2))*V (slice p R (point w.1 w.2))/(w.2:ℂ)^(2 : ℕ)) (cell Y) := by
    intro w hw
    have hy : 0<w.2 := by linarith [hw.2.1]
    have hu := (hU (slice p R (point w.1 w.2)) hp hr (by simpa [slice,point] using hy)).continuousAt.comp
      (f := fun v : ℝ×ℝ => slice p R (point v.1 v.2)) (x := w) hm.continuousAt
    have hv := (hV (slice p R (point w.1 w.2)) hp hr (by simpa [slice,point] using hy)).continuousAt.comp
      (f := fun v : ℝ×ℝ => slice p R (point v.1 v.2)) (x := w) hm.continuousAt
    exact ((hu.mul hv).div (by fun_prop)
      (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr hy.ne'))).continuousWithinAt
  exact (hc.mono (domain_subset_cell Y)).integrableOn_compact (isCompact_domain Y)

/-- The complete scalar Green transfer on the original modular domain has only
its cusp-top flux; neither source nor reader is replaced by a principal mode. -/
private theorem scalar_green_top (U V : F) (p R : ℝ) (hp : 0<p) (hr : 1<R)
    (hU : ExteriorSmooth U) (hmU : ExteriorModular U)
    (hV : ExteriorSmooth V) (hmV : ExteriorModular V) {Y : ℝ} (hY : 1≤Y) :
    scalarPeriod (angularLap U) V p R Y-scalarPeriod U (angularLap V) p R Y=
      topFlux V U p R Y-topFlux U V p R Y := by
  have h := scalar_green_integral U V p R
    (fun z hz => hU _ hp hr hz) (fun z hz => hV _ hp hr hz) hY
  rw [boundary_eq_top V U p R hp hr hmV hU hmU hY,
    boundary_eq_top U V p R hp hr hmU hV hmV hY] at h
  have hfirst : (∫ w in domain Y, scalarDensity V U (slice p R (point w.1 w.2)))=
      scalarPeriod (angularLap U) V p R Y := by
    unfold scalarPeriod
    apply setIntegral_congr_fun (isCompact_domain Y).measurableSet
    intro w hw
    have hy : 0<w.2 := by linarith [hw.1.2.1]
    dsimp only
    rw [scalarDensity_eq _ _ _ (by simpa [slice,point] using hy)]
    rw [show (slice p R (point w.1 w.2)) 3=w.2 by simp [slice,point]]
    ring
  have hsecond : (∫ w in domain Y, scalarDensity U V (slice p R (point w.1 w.2)))=
      scalarPeriod U (angularLap V) p R Y := by
    unfold scalarPeriod
    apply setIntegral_congr_fun (isCompact_domain Y).measurableSet
    intro w hw
    have hy : 0<w.2 := by linarith [hw.1.2.1]
    dsimp only
    simpa [slice,point] using scalarDensity_eq U V (slice p R (point w.1 w.2))
      (by simpa [slice,point] using hy)
  rw [hfirst,hsecond] at h
  exact h

/-- Moving the source Laplacian onto either orbit derivative of the unchanged
physical reader retains the exact antisymmetric top flux. -/
theorem original_source_orbit_green (q r : XiZeroCopy) (branch side outer : Bool) (amp : ℂ)
    (p R : ℝ) (hp : 0<p) (hr : 1<R) {Y : ℝ} (hY : 1≤Y) (j : Fin 2) :
    let U := sourceScalar q branch amp
    let E := orbitDerivative (leftScalar r side outer) j
    scalarPeriod (angularLap U) E p R Y-eigenvalue r*scalarPeriod U E p R Y=
      topFlux E U p R Y-topFlux U E p R Y := by
  dsimp only
  have h := scalar_green_top (sourceScalar q branch amp)
    (orbitDerivative (leftScalar r side outer) j) p R hp hr
    (source_smooth q branch amp) (source_modular q branch amp)
    (orbit_smooth (reader_smooth r side outer) j)
    (orbit_modular (reader_smooth r side outer) (reader_modular r side outer) j) hY
  have he : scalarPeriod (sourceScalar q branch amp)
      (angularLap (orbitDerivative (leftScalar r side outer) j)) p R Y=
      eigenvalue r*scalarPeriod (sourceScalar q branch amp)
        (orbitDerivative (leftScalar r side outer) j) p R Y := by
    rw [scalarPeriod,scalarPeriod,← integral_const_mul]
    apply setIntegral_congr_fun (isCompact_domain Y).measurableSet
    intro w hw
    have hy : 0<w.2 := by linarith [hw.1.2.1]
    dsimp only
    rw [left_orbit_angular r side outer _ hr (by simpa [slice,point] using hy)]
    ring
  rw [he] at h
  exact h

/-- The full original forcing remains in the scalar period after the source
Laplacian is transferred, together with its source-determined normal flux. -/
theorem original_forced_orbit_period (q r : XiZeroCopy) (branch side outer : Bool) (amp : ℂ)
    (p R : ℝ) (hp : 0<p) (hr : 1<R) {Y : ℝ} (hY : 1≤Y) (j : Fin 2) :
    let U := sourceScalar q branch amp
    let E := orbitDerivative (leftScalar r side outer) j
    scalarPeriod (forcedContact q branch amp) E p R Y=
      (eigenvalue r-2)*scalarPeriod U E p R Y+
      (R:ℂ)^(3 : ℕ)/((R:ℂ)^(2 : ℕ)-1)*scalarPeriod (D4BMOriginalSourceContact.originalForcing q branch amp) E p R Y+
      (topFlux E U p R Y-topFlux U E p R Y) := by
  dsimp only
  let U := sourceScalar q branch amp
  let E := orbitDerivative (leftScalar r side outer) j
  let D := forcedContact q branch amp
  have hU := period_integrable U E p R Y hp hr (source_smooth q branch amp)
    (orbit_smooth (reader_smooth r side outer) j)
  have hL := period_integrable (angularLap U) E p R Y hp hr (lap_smooth (source_smooth q branch amp))
    (orbit_smooth (reader_smooth r side outer) j)
  have hD := period_integrable D E p R Y hp hr (forced_smooth q branch amp)
    (orbit_smooth (reader_smooth r side outer) j)
  have hf : scalarPeriod D E p R Y+2*scalarPeriod U E p R Y-
      scalarPeriod (angularLap U) E p R Y=
      (R:ℂ)^(3 : ℕ)/((R:ℂ)^(2 : ℕ)-1)*scalarPeriod (D4BMOriginalSourceContact.originalForcing q branch amp) E p R Y := by
    have hi := integral_sub (hD.add (hU.const_mul 2)) hL
    simp only [Pi.add_apply] at hi
    rw [integral_add hD (hU.const_mul 2),integral_const_mul] at hi
    simp only [scalarPeriod] at ⊢
    rw [← hi,← integral_const_mul]
    apply setIntegral_congr_fun (isCompact_domain Y).measurableSet
    intro w hw
    dsimp only [D,forcedContact,U,slice]
    simp only [Matrix.cons_val_one,Matrix.cons_val_zero]
    ring
  have hg := original_source_orbit_green q r branch side outer amp p R hp hr hY j
  dsimp only at hg
  change scalarPeriod (angularLap U) E p R Y-eigenvalue r*scalarPeriod U E p R Y=
    topFlux E U p R Y-topFlux U E p R Y at hg
  change scalarPeriod D E p R Y=_
  linear_combination hf+hg

/-- All three source-derived angular transfers in the fully reduced metric current. -/
def completeTopFlux (q r : XiZeroCopy) (branch side outer : Bool) (amp : ℂ)
    (j : Fin 2) (p R Y : ℝ) : ℂ :=
  let U := sourceScalar q branch amp
  let W := leftScalar r side outer
  let E := orbitDerivative W j
  topFlux (orbitDerivative U j) (scalarContact W) p R Y-
    topFlux (forcedContact q branch amp) E p R Y+
    eigenvalue r*(topFlux E U p R Y-topFlux U E p R Y)

/-- Exact finite-domain identification of the original Einstein current with
the scalar symplectic density, full forcing, and complete top normal flux. -/
theorem original_metric_complete_scalar_integral (q r : XiZeroCopy)
    (branch side outer : Bool) (amp : ℂ) (p R : ℝ) (hp : 0<p) (hr : 1<R)
    {Y : ℝ} (hY : 1≤Y) (j : Fin 2) :
    let U := sourceScalar q branch amp
    let W := leftScalar r side outer
    let E := orbitDerivative W j
    (∫ w in domain Y, metricDensity q r branch side outer amp j (slice p R (point w.1 w.2)))=
      1/(R:ℂ)^(2 : ℕ)*((eigenvalue r*(eigenvalue r-2))*
        (scalarPeriod U E p R Y-scalarPeriod (orbitDerivative U j) W p R Y)+
        eigenvalue r*((R:ℂ)^(3 : ℕ)/((R:ℂ)^(2 : ℕ)-1))*
          scalarPeriod (D4BMOriginalSourceContact.originalForcing q branch amp) E p R Y+
        completeTopFlux q r branch side outer amp j p R Y) := by
  have h := original_metric_top_integral q r branch side outer amp p R hp hr hY j
  have hf := original_forced_orbit_period q r branch side outer amp p R hp hr hY j
  dsimp only at h hf ⊢
  rw [hf] at h
  dsimp only [completeTopFlux]
  linear_combination h

private theorem original_forcing_smooth (q : XiZeroCopy) (branch : Bool) (amp : ℂ) :
    ExteriorSmooth (D4BMOriginalSourceContact.originalForcing q branch amp) := by
  intro x hp hr hy
  let U := sourceScalar q branch amp
  have he : D4BMOriginalSourceContact.originalForcing q branch amp =ᶠ[𝓝 x]
      fun z => (((z 1:ℂ)^(2 : ℕ)-1)/(z 1:ℂ)^(3 : ℕ))*
        (scalarContact U z-angularLap U z+2*U z) := by
    filter_upwards [(isOpen_lt continuous_const (continuous_apply 0)).mem_nhds hp,
      (isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hr,
      (isOpen_lt continuous_const (continuous_apply 3)).mem_nhds hy] with z hz0 hz1 hz3
    have hc := original_scalar_contact q branch amp z hz0 hz1 hz3
    have hh : scalarContact U z-angularLap U z+2*U z=
        (z 1:ℂ)^(3 : ℕ)/((z 1:ℂ)^(2 : ℕ)-1)*D4BMOriginalSourceContact.originalForcing q branch amp z := by
      dsimp only [U]
      linear_combination hc
    rw [hh]
    have hR : (z 1:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (by linarith)
    have hf : (z 1:ℂ)^(2 : ℕ)-1≠0 := by exact_mod_cast (show (z 1)^(2 : ℕ)-1≠0 by nlinarith)
    field_simp [hR,hf]
  have hR : ContDiffAt ℝ ∞ (fun z : P => z 1) x :=
    (contDiff_apply ℝ ℝ (1:Fin 4)).contDiffAt
  have hnum : ContDiffAt ℝ ∞ (fun z : P => (z 1)^(2 : ℕ)-1) x :=
    (hR.pow 2).sub contDiffAt_const
  have hreal := hnum.div (hR.pow 3) (pow_ne_zero 3 (show x 1≠0 by linarith))
  have hs : ContDiffAt ℝ ∞ (fun z : P => ((z 1:ℂ)^(2 : ℕ)-1)/(z 1:ℂ)^(3 : ℕ)) x := by
    have hc := Complex.ofRealCLM.contDiff.contDiffAt.comp x hreal
    change ContDiffAt ℝ ∞ (fun z : P => ((((z 1)^(2 : ℕ)-1)/(z 1)^(3 : ℕ):ℝ):ℂ)) x at hc
    simpa only [Complex.ofReal_div,Complex.ofReal_sub,Complex.ofReal_pow,Complex.ofReal_one] using! hc
  have hv : ContDiffAt ℝ ∞ (fun z => scalarContact U z-angularLap U z+2*U z) x :=
    ((contact_smooth (source_smooth q branch amp) x hp hr hy).sub
      (lap_smooth (source_smooth q branch amp) x hp hr hy)).add
      (contDiffAt_const.mul (source_smooth q branch amp x hp hr hy))
  exact (hs.mul hv).congr_of_eventuallyEq he

private theorem period_orbit_left (U V : F) (p R Y : ℝ) (hp : 0<p) (hr : 1<R)
    (hU : ExteriorSmooth U) (hV : ExteriorSmooth V) :
    scalarPeriod (orbitDerivative U 1) V p R Y=
      ((R:ℂ)^(2 : ℕ)-1)*scalarPeriod (orbitDerivative U 0) V p R Y+
        scalarPeriod (coordDeriv 0 U) V p R Y := by
  have hR := period_integrable (orbitDerivative U 0) V p R Y hp hr (orbit_smooth hU 0) hV
  have hp' := period_integrable (coordDeriv 0 U) V p R Y hp hr (smooth_partial hU 0) hV
  simp only [scalarPeriod,← integral_const_mul]
  rw [← integral_add (hR.const_mul ((R:ℂ)^(2 : ℕ)-1)) hp']
  apply setIntegral_congr_fun (isCompact_domain Y).measurableSet
  intro w hw
  simp only [orbitDerivative,one_ne_zero,ite_false,ite_true,slice,Matrix.cons_val_one,Matrix.cons_val_zero]
  ring

private theorem period_orbit_right (U V : F) (p R Y : ℝ) (hp : 0<p) (hr : 1<R)
    (hU : ExteriorSmooth U) (hV : ExteriorSmooth V) :
    scalarPeriod U (orbitDerivative V 1) p R Y=
      ((R:ℂ)^(2 : ℕ)-1)*scalarPeriod U (orbitDerivative V 0) p R Y+
        scalarPeriod U (coordDeriv 0 V) p R Y := by
  have hR := period_integrable U (orbitDerivative V 0) p R Y hp hr hU (orbit_smooth hV 0)
  have hp' := period_integrable U (coordDeriv 0 V) p R Y hp hr hU (smooth_partial hV 0)
  simp only [scalarPeriod,← integral_const_mul]
  rw [← integral_add (hR.const_mul ((R:ℂ)^(2 : ℕ)-1)) hp']
  apply setIntegral_congr_fun (isCompact_domain Y).measurableSet
  intro w hw
  simp only [orbitDerivative,one_ne_zero,ite_false,ite_true,slice,Matrix.cons_val_one,Matrix.cons_val_zero]
  ring

private theorem coordinate_update (F : (Fin 4 → ℝ) → ℂ) (x : Fin 4 → ℝ) (i : Fin 4)
    (hf : DifferentiableAt ℝ F x) :
    coordDeriv i F x=deriv (fun a => F (Function.update x i a)) (x i) := by
  have hf' : HasFDerivAt F (fderiv ℝ F x) (Function.update x i (x i)) := by
    simpa only [Function.update_eq_self] using hf.hasFDerivAt
  have h := hf'.comp_hasDerivAt (x i) (hasDerivAt_update x i (x i))
  simpa only [Function.update_eq_self,coordDeriv,Function.comp_def] using h.deriv.symm

/-- The temporal derivative of the unchanged physical left mode has its actual
QNM frequency, before any integration or continuation of the current. -/
theorem original_reader_time_derivative (r : XiZeroCopy) (side outer : Bool) (x : P)
    (hr : 1<x 1) (hy : 0<x 3) :
    coordDeriv 0 (leftScalar r side outer) x= -frequency r side*leftScalar r side outer x := by
  rw [coordinate_update _ _ _ ((leftScalar_smooth r side outer x hr hy).differentiableAt (by simp))]
  simp_rw [leftScalar_value]
  simp only [angularPoint,Function.update_self,
    Function.update_of_ne (by decide : (1:Fin 4)≠0),
    Function.update_of_ne (by decide : (2:Fin 4)≠0),
    Function.update_of_ne (by decide : (3:Fin 4)≠0)]
  have he := (((hasDerivAt_id (x 0)).sub_const (D4BMIngoingCoordinates.tortoise (x 1))).ofReal_comp.const_mul
    (-frequency r side)).cexp
  have hd := ((he.mul_const (D4BMPhysicalModeAction.radiusLift (profile r side outer) (x 1))).mul_const
    (D4BMLiteralCusp.scalar (physicalAngularParameter r) ![x 2,x 3])).deriv
  calc
    _ = Complex.exp (-frequency r side*((x 0-D4BMIngoingCoordinates.tortoise (x 1)):ℂ))*
        (-frequency r side)*D4BMPhysicalModeAction.radiusLift (profile r side outer) (x 1)*
        D4BMLiteralCusp.scalar (physicalAngularParameter r) ![x 2,x 3] := by
      simpa only [id_eq,Complex.ofReal_one,mul_one,Complex.ofReal_sub] using! hd
    _ = _ := by ring

private theorem period_reader_time (U : F) (r : XiZeroCopy) (side outer : Bool)
    (p R Y : ℝ) (hr : 1<R) :
    scalarPeriod U (coordDeriv 0 (leftScalar r side outer)) p R Y=
      -frequency r side*scalarPeriod U (leftScalar r side outer) p R Y := by
  simp only [scalarPeriod,← integral_const_mul]
  apply setIntegral_congr_fun (isCompact_domain Y).measurableSet
  intro w hw
  have hy : 0<w.2 := by linarith [hw.1.2.1]
  dsimp only
  rw [original_reader_time_derivative r side outer _ hr (by simpa [slice,point] using hy)]
  ring

/-- The original static-time combination of the two metric-current integrals
equals the forced scalar temporal density with its complete normal flux.
Ingoing time and exterior radius remain fixed; the angular cutoff is finite. -/
theorem original_static_metric_scalar_integral (q r : XiZeroCopy)
    (branch side outer : Bool) (amp : ℂ) (p R : ℝ) (hp : 0<p) (hr : 1<R)
    {Y : ℝ} (hY : 1≤Y) :
    let U := sourceScalar q branch amp
    let W := leftScalar r side outer
    let f := (R:ℂ)^(2 : ℕ)-1
    let μ := eigenvalue r
    let w := frequency r side
    (∫ z in domain Y, metricDensity q r branch side outer amp 0 (slice p R (point z.1 z.2)))-
      (∫ z in domain Y, metricDensity q r branch side outer amp 1 (slice p R (point z.1 z.2)))/f=
      μ*(μ-2)/((R:ℂ)^(2 : ℕ)*f)*
        (scalarPeriod (coordDeriv 0 U) W p R Y+w*scalarPeriod U W p R Y)+
      μ*(R:ℂ)*w/f^(2 : ℕ)*scalarPeriod (D4BMOriginalSourceContact.originalForcing q branch amp) W p R Y+
      (completeTopFlux q r branch side outer amp 0 p R Y-
        completeTopFlux q r branch side outer amp 1 p R Y/f)/(R:ℂ)^(2 : ℕ) := by
  dsimp only
  rw [original_metric_complete_scalar_integral q r branch side outer amp p R hp hr hY 0,
    original_metric_complete_scalar_integral q r branch side outer amp p R hp hr hY 1]
  rw [period_orbit_left _ _ p R Y hp hr (source_smooth q branch amp) (reader_smooth r side outer),
    period_orbit_right _ _ p R Y hp hr (source_smooth q branch amp) (reader_smooth r side outer),
    period_orbit_right _ _ p R Y hp hr (original_forcing_smooth q branch amp) (reader_smooth r side outer),
    period_reader_time _ r side outer p R Y hr,period_reader_time _ r side outer p R Y hr]
  have hR : (R:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (by linarith)
  have hf : (R:ℂ)^(2 : ℕ)-1≠0 := by exact_mod_cast (show R^(2 : ℕ)-1≠0 by nlinarith)
  field_simp [hR,hf]
  ring

private theorem mode_smooth (q : XiZeroCopy) (w : ℂ) (hw : w.im≠0) (outer : Bool) :
    ExteriorSmooth (modeScalar q w outer) := by
  intro x hp hr hy
  exact modeScalar_smooth q w hw outer x hr hy

private theorem mode_modular (q : XiZeroCopy) (w : ℂ) (outer : Bool) :
    ExteriorModular (modeScalar q w outer) := by
  intro p R hp hr A z
  rw [modeScalar_value,modeScalar_value]
  have h := physicalScalar_modular q A z
  change D4BMLiteralCusp.scalar (physicalAngularParameter q) (angularPoint (slice p R ((A • z:UpperHalfPlane):ℂ)))=
    D4BMLiteralCusp.scalar (physicalAngularParameter q) (angularPoint (slice p R z)) at h
  simp only [slice,Matrix.cons_val_zero,Matrix.cons_val_one] at h ⊢
  rw [h]

private theorem mode_pairing_smooth (U V : F) (hU : ExteriorSmooth U) (hV : ExteriorSmooth V) :
    ExteriorSmooth (pairing U V) := by
  intro x hp hr hy
  change ContDiffAt ℝ ∞ (fun z => ∑ j : Fin 2, coexactField U j z*coexactField V j z) x
  simp only [Fin.sum_univ_two,coexactField,ite_true,one_ne_zero,ite_false]
  exact ((smooth_partial hU 3 x hp hr hy).mul (smooth_partial hV 3 x hp hr hy)).add
    ((smooth_partial hU 2 x hp hr hy).neg.mul (smooth_partial hV 2 x hp hr hy).neg)

private theorem mode_area_integrable (U : F) (hU : ExteriorSmooth U)
    (p R Y : ℝ) (hp : 0<p) (hr : 1<R) :
    IntegrableOn (fun v : ℝ×ℝ => U (slice p R (point v.1 v.2))) (domain Y) := by
  have hm : Continuous (fun v : ℝ×ℝ => slice p R (point v.1 v.2)) := by
    unfold slice point
    fun_prop
  have hc : ContinuousOn (fun v : ℝ×ℝ => U (slice p R (point v.1 v.2))) (cell Y) := by
    intro v hv
    have hy : 0<v.2 := by linarith [hv.2.1]
    exact ((hU _ hp hr (by simpa [slice,point] using hy)).continuousAt.comp
      (f := fun v : ℝ×ℝ => slice p R (point v.1 v.2)) (x := v) hm.continuousAt).continuousWithinAt
  exact (hc.mono (domain_subset_cell Y)).integrableOn_compact (isCompact_domain Y)

/-- The original metric-family current retains its full angular boundary before
any temporal continuation or horizon limit. -/
theorem mode_metric_top_integral (q r : XiZeroCopy) (branch outer : Bool) (amp w : ℂ)
    (hw : w.im≠0) (p R : ℝ) (hp : 0<p) (hr : 1<R) {Y : ℝ} (hY : 1≤Y) (j : Fin 2) :
    let U := sourceScalar q branch amp
    let W := modeScalar r w outer
    let A := orbitDerivative U j
    let D := forcedContact q branch amp
    let E := orbitDerivative W j
    (∫ v in domain Y, modeMetricDensity q r branch outer amp w j (slice p R (point v.1 v.2)))+
      1/(R:ℂ)^(2 : ℕ)*(eigenvalue r*(eigenvalue r-2)*scalarPeriod A W p R Y-
        eigenvalue r*scalarPeriod D E p R Y)=
      1/(R:ℂ)^(2 : ℕ)*(topFlux A (scalarContact W) p R Y-topFlux D E p R Y) := by
  dsimp only
  let U := sourceScalar q branch amp
  let W := modeScalar r w outer
  let A := orbitDerivative U j
  let B := scalarContact W
  let D := forcedContact q branch amp
  let E := orbitDerivative W j
  have hA := orbit_smooth (source_smooth q branch amp) j
  have hB := contact_smooth (mode_smooth r w hw outer)
  have hD := forced_smooth q branch amp
  have hE := orbit_smooth (mode_smooth r w hw outer) j
  have hab := coexact_pairing_integral A B p R (fun z hz => hA _ hp hr hz)
    (fun z hz => hB _ hp hr hz) hY
  have hde := coexact_pairing_integral D E p R (fun z hz => hD _ hp hr hz)
    (fun z hz => hE _ hp hr hz) hY
  rw [boundary_eq_top A B p R hp hr
    (orbit_modular (source_smooth q branch amp) (source_modular q branch amp) j)
    hB (contact_modular (mode_smooth r w hw outer) (mode_modular r w outer)) hY] at hab
  rw [boundary_eq_top D E p R hp hr (forced_modular q branch amp) hE
    (orbit_modular (mode_smooth r w hw outer) (mode_modular r w outer) j) hY] at hde
  have habs : (∫ v in domain Y, scalarDensity A B (slice p R (point v.1 v.2)))=
      eigenvalue r*(eigenvalue r-2)*scalarPeriod A W p R Y := by
    rw [scalarPeriod,← integral_const_mul]
    apply setIntegral_congr_fun (isCompact_domain Y).measurableSet
    intro v hv
    have hy : 0<(slice p R (point v.1 v.2)) 3 := by
      simpa [slice,point] using (show 0<v.2 by linarith [hv.1.2.1])
    dsimp only
    rw [scalarDensity_eq _ _ _ hy]
    dsimp only [B,W]
    rw [mode_contact_angular r w hw outer _ hr hy]
    simp only [slice,point,Matrix.cons_val,Complex.add_im,Complex.ofReal_im,
      Complex.mul_I_im,Complex.ofReal_re,zero_add]
    ring
  have hdes : (∫ v in domain Y, scalarDensity D E (slice p R (point v.1 v.2)))=
      eigenvalue r*scalarPeriod D E p R Y := by
    rw [scalarPeriod,← integral_const_mul]
    apply setIntegral_congr_fun (isCompact_domain Y).measurableSet
    intro v hv
    have hy : 0<(slice p R (point v.1 v.2)) 3 := by
      simpa [slice,point] using (show 0<v.2 by linarith [hv.1.2.1])
    dsimp only
    rw [scalarDensity_eq _ _ _ hy]
    dsimp only [E,W]
    rw [mode_orbit_angular r w hw outer _ hr hy]
    simp only [slice,point,Matrix.cons_val,Complex.add_im,Complex.ofReal_im,
      Complex.mul_I_im,Complex.ofReal_re,zero_add]
    ring
  have hi : (∫ v in domain Y, modeMetricDensity q r branch outer amp w j (slice p R (point v.1 v.2)))=
      1/(R:ℂ)^(2 : ℕ)*((∫ v in domain Y, pairing A B (slice p R (point v.1 v.2)))-
        ∫ v in domain Y, pairing D E (slice p R (point v.1 v.2))) := by
    rw [← integral_sub (mode_area_integrable _ (mode_pairing_smooth A B hA hB) p R Y hp hr)
      (mode_area_integrable _ (mode_pairing_smooth D E hD hE) p R Y hp hr),← integral_const_mul]
    apply setIntegral_congr_fun (isCompact_domain Y).measurableSet
    intro v hv
    have hy : 0<(slice p R (point v.1 v.2)) 3 := by
      simpa [slice,point] using (show 0<v.2 by linarith [hv.1.2.1])
    exact mode_metric_density q r branch outer amp w hw _ hp hr hy j
  rw [habs] at hab
  rw [hdes] at hde
  rw [hi]
  linear_combination (1/(R:ℂ)^(2 : ℕ))*hab-(1/(R:ℂ)^(2 : ℕ))*hde

/-- Moving the source Laplacian onto either orbit derivative of the unchanged
physical reader retains the exact antisymmetric top flux. -/
theorem mode_source_orbit_green (q r : XiZeroCopy) (branch outer : Bool) (amp w : ℂ) (hw : w.im≠0)
    (p R : ℝ) (hp : 0<p) (hr : 1<R) {Y : ℝ} (hY : 1≤Y) (j : Fin 2) :
    let U := sourceScalar q branch amp
    let E := orbitDerivative (modeScalar r w outer) j
    scalarPeriod (angularLap U) E p R Y-eigenvalue r*scalarPeriod U E p R Y=
      topFlux E U p R Y-topFlux U E p R Y := by
  dsimp only
  have h := scalar_green_top (sourceScalar q branch amp)
    (orbitDerivative (modeScalar r w outer) j) p R hp hr
    (source_smooth q branch amp) (source_modular q branch amp)
    (orbit_smooth (mode_smooth r w hw outer) j)
    (orbit_modular (mode_smooth r w hw outer) (mode_modular r w outer) j) hY
  have he : scalarPeriod (sourceScalar q branch amp)
      (angularLap (orbitDerivative (modeScalar r w outer) j)) p R Y=
      eigenvalue r*scalarPeriod (sourceScalar q branch amp)
        (orbitDerivative (modeScalar r w outer) j) p R Y := by
    rw [scalarPeriod,scalarPeriod,← integral_const_mul]
    apply setIntegral_congr_fun (isCompact_domain Y).measurableSet
    intro v hv
    have hy : 0<v.2 := by linarith [hv.1.2.1]
    dsimp only
    rw [mode_orbit_angular r w hw outer _ hr (by simpa [slice,point] using hy)]
    ring
  rw [he] at h
  exact h

/-- The full original forcing remains in the scalar period after the source
Laplacian is transferred, together with its source-determined normal flux. -/
theorem mode_forced_orbit_period (q r : XiZeroCopy) (branch outer : Bool) (amp w : ℂ) (hw : w.im≠0)
    (p R : ℝ) (hp : 0<p) (hr : 1<R) {Y : ℝ} (hY : 1≤Y) (j : Fin 2) :
    let U := sourceScalar q branch amp
    let E := orbitDerivative (modeScalar r w outer) j
    scalarPeriod (forcedContact q branch amp) E p R Y=
      (eigenvalue r-2)*scalarPeriod U E p R Y+
      (R:ℂ)^(3 : ℕ)/((R:ℂ)^(2 : ℕ)-1)*scalarPeriod (D4BMOriginalSourceContact.originalForcing q branch amp) E p R Y+
      (topFlux E U p R Y-topFlux U E p R Y) := by
  dsimp only
  let U := sourceScalar q branch amp
  let E := orbitDerivative (modeScalar r w outer) j
  let D := forcedContact q branch amp
  have hU := period_integrable U E p R Y hp hr (source_smooth q branch amp)
    (orbit_smooth (mode_smooth r w hw outer) j)
  have hL := period_integrable (angularLap U) E p R Y hp hr (lap_smooth (source_smooth q branch amp))
    (orbit_smooth (mode_smooth r w hw outer) j)
  have hD := period_integrable D E p R Y hp hr (forced_smooth q branch amp)
    (orbit_smooth (mode_smooth r w hw outer) j)
  have hf : scalarPeriod D E p R Y+2*scalarPeriod U E p R Y-
      scalarPeriod (angularLap U) E p R Y=
      (R:ℂ)^(3 : ℕ)/((R:ℂ)^(2 : ℕ)-1)*scalarPeriod (D4BMOriginalSourceContact.originalForcing q branch amp) E p R Y := by
    have hi := integral_sub (hD.add (hU.const_mul 2)) hL
    simp only [Pi.add_apply] at hi
    rw [integral_add hD (hU.const_mul 2),integral_const_mul] at hi
    simp only [scalarPeriod] at ⊢
    rw [← hi,← integral_const_mul]
    apply setIntegral_congr_fun (isCompact_domain Y).measurableSet
    intro v hv
    dsimp only [D,forcedContact,U,slice]
    simp only [Matrix.cons_val_one,Matrix.cons_val_zero]
    ring
  have hg := mode_source_orbit_green q r branch outer amp w hw p R hp hr hY j
  dsimp only at hg
  change scalarPeriod (angularLap U) E p R Y-eigenvalue r*scalarPeriod U E p R Y=
    topFlux E U p R Y-topFlux U E p R Y at hg
  change scalarPeriod D E p R Y=_
  linear_combination hf+hg

/-- All three source-derived angular transfers in the fully reduced metric current. -/
def modeCompleteTopFlux (q r : XiZeroCopy) (branch outer : Bool) (amp w : ℂ)
    (j : Fin 2) (p R Y : ℝ) : ℂ :=
  let U := sourceScalar q branch amp
  let W := modeScalar r w outer
  let E := orbitDerivative W j
  topFlux (orbitDerivative U j) (scalarContact W) p R Y-
    topFlux (forcedContact q branch amp) E p R Y+
    eigenvalue r*(topFlux E U p R Y-topFlux U E p R Y)

/-- Exact finite-domain identification of the original Einstein current with
the scalar symplectic density, full forcing, and complete top normal flux. -/
theorem mode_metric_complete_scalar_integral (q r : XiZeroCopy)
    (branch outer : Bool) (amp w : ℂ) (hw : w.im≠0) (p R : ℝ) (hp : 0<p) (hr : 1<R)
    {Y : ℝ} (hY : 1≤Y) (j : Fin 2) :
    let U := sourceScalar q branch amp
    let W := modeScalar r w outer
    let E := orbitDerivative W j
    (∫ v in domain Y, modeMetricDensity q r branch outer amp w j (slice p R (point v.1 v.2)))=
      1/(R:ℂ)^(2 : ℕ)*((eigenvalue r*(eigenvalue r-2))*
        (scalarPeriod U E p R Y-scalarPeriod (orbitDerivative U j) W p R Y)+
        eigenvalue r*((R:ℂ)^(3 : ℕ)/((R:ℂ)^(2 : ℕ)-1))*
          scalarPeriod (D4BMOriginalSourceContact.originalForcing q branch amp) E p R Y+
        modeCompleteTopFlux q r branch outer amp w j p R Y) := by
  have h := mode_metric_top_integral q r branch outer amp w hw p R hp hr hY j
  have hf := mode_forced_orbit_period q r branch outer amp w hw p R hp hr hY j
  dsimp only at h hf ⊢
  rw [hf] at h
  dsimp only [modeCompleteTopFlux]
  linear_combination h

private theorem mode_period_time (U : F) (r : XiZeroCopy) (w : ℂ) (hw : w.im≠0) (outer : Bool)
    (p R Y : ℝ) (hr : 1<R) :
    scalarPeriod U (coordDeriv 0 (modeScalar r w outer)) p R Y=
      -w*scalarPeriod U (modeScalar r w outer) p R Y := by
  simp only [scalarPeriod,← integral_const_mul]
  apply setIntegral_congr_fun (isCompact_domain Y).measurableSet
  intro v hv
  have hy : 0<v.2 := by linarith [hv.1.2.1]
  dsimp only
  rw [mode_time_derivative r w hw outer _ hr (by simpa [slice,point] using hy)]
  ring

/-- The original static-time combination of the two metric-current integrals
equals the forced scalar temporal density with its complete normal flux.
Ingoing time and exterior radius remain fixed; the angular cutoff is finite. -/
theorem mode_static_metric_scalar_integral (q r : XiZeroCopy)
    (branch outer : Bool) (amp w : ℂ) (hw : w.im≠0) (p R : ℝ) (hp : 0<p) (hr : 1<R)
    {Y : ℝ} (hY : 1≤Y) :
    let U := sourceScalar q branch amp
    let W := modeScalar r w outer
    let f := (R:ℂ)^(2 : ℕ)-1
    let μ := eigenvalue r
    (∫ z in domain Y, modeMetricDensity q r branch outer amp w 0 (slice p R (point z.1 z.2)))-
      (∫ z in domain Y, modeMetricDensity q r branch outer amp w 1 (slice p R (point z.1 z.2)))/f=
      μ*(μ-2)/((R:ℂ)^(2 : ℕ)*f)*
        (scalarPeriod (coordDeriv 0 U) W p R Y+w*scalarPeriod U W p R Y)+
      μ*(R:ℂ)*w/f^(2 : ℕ)*scalarPeriod (D4BMOriginalSourceContact.originalForcing q branch amp) W p R Y+
      (modeCompleteTopFlux q r branch outer amp w 0 p R Y-
        modeCompleteTopFlux q r branch outer amp w 1 p R Y/f)/(R:ℂ)^(2 : ℕ) := by
  dsimp only
  rw [mode_metric_complete_scalar_integral q r branch outer amp w hw p R hp hr hY 0,
    mode_metric_complete_scalar_integral q r branch outer amp w hw p R hp hr hY 1]
  rw [period_orbit_left _ _ p R Y hp hr (source_smooth q branch amp) (mode_smooth r w hw outer),
    period_orbit_right _ _ p R Y hp hr (source_smooth q branch amp) (mode_smooth r w hw outer),
    period_orbit_right _ _ p R Y hp hr (original_forcing_smooth q branch amp) (mode_smooth r w hw outer),
    mode_period_time _ r w hw outer p R Y hr,mode_period_time _ r w hw outer p R Y hr]
  have hR : (R:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (by linarith)
  have hf : (R:ℂ)^(2 : ℕ)-1≠0 := by exact_mod_cast (show R^(2 : ℕ)-1≠0 by nlinarith)
  field_simp [hR,hf]
  ring
/-- Exact specialization of the complete family flux to the prescribed QNM. -/
theorem modeCompleteTopFlux_specialize (q r : XiZeroCopy) (branch side outer : Bool) (amp : ℂ) :
    modeCompleteTopFlux q r branch outer amp (frequency r side)=
      completeTopFlux q r branch side outer amp := rfl


private theorem slice_clock_derivative (H : F) (p R : ℝ) (z : ℂ)
    (hH : DifferentiableAt ℝ H (slice p R z)) :
    HasDerivAt (fun t => H (slice t R z)) (coordDeriv 0 H (slice p R z)) p := by
  have hc : HasDerivAt (fun t => slice t R z) (Pi.single 0 1) p := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · simpa [slice,Pi.single_apply,Fin.ext_iff] using! hasDerivAt_id p
    · simpa [slice,Pi.single_apply,Fin.ext_iff] using hasDerivAt_const p R
    · simpa [slice,Pi.single_apply,Fin.ext_iff] using hasDerivAt_const p z.re
    · simpa [slice,Pi.single_apply,Fin.ext_iff] using hasDerivAt_const p z.im
  exact hH.hasFDerivAt.comp_hasDerivAt p hc

/-- Actual finite-time transfer of the original source derivative onto the
independent-frequency reader, retaining both original endpoint values.
This identity is formed before any angular finite part or horizon limit. -/
theorem mode_time_transfer (q r : XiZeroCopy) (branch outer : Bool) (amp w : ℂ)
    (hw : w.im≠0) (a b R : ℝ) (ha : 0<a) (hab : a≤b) (hr : 1<R)
    (z : ℂ) (hz : 0<z.im) :
    let U := sourceScalar q branch amp
    let W := modeScalar r w outer
    (∫ p in a..b, (coordDeriv 0 U (slice p R z)+w*U (slice p R z))*W (slice p R z))=
      U (slice b R z)*W (slice b R z)-U (slice a R z)*W (slice a R z)+
        2*w*(∫ p in a..b, U (slice p R z)*W (slice p R z)) := by
  dsimp only
  let U := sourceScalar q branch amp
  let W := modeScalar r w outer
  let d := fun p => (coordDeriv 0 U (slice p R z)-w*U (slice p R z))*W (slice p R z)
  let v := fun p => U (slice p R z)*W (slice p R z)
  have hmap : Continuous (fun p => slice p R z) := by
    unfold slice
    fun_prop
  have hu (p : ℝ) (hp : p∈Icc a b) := source_smooth q branch amp (slice p R z) (ha.trans_le hp.1) hr hz
  have hW (p : ℝ) (hp : p∈Icc a b) := mode_smooth r w hw outer (slice p R z) (ha.trans_le hp.1) hr hz
  have hd : ContinuousOn d (Icc a b) := by
    intro p hp
    have hU := hu p hp
    have hV := hW p hp
    have hpartial : ContDiffAt ℝ ∞ (coordDeriv 0 U) (slice p R z) :=
      coordDeriv_contDiffAt hU (by simp) 0
    exact (((hpartial.continuousAt.sub (hU.continuousAt.const_mul w)).mul hV.continuousAt).comp
      (f := fun p => slice p R z) (x := p) hmap.continuousAt).continuousWithinAt
  have hv : ContinuousOn v (Icc a b) := by
    intro p hp
    exact (((hu p hp).continuousAt.mul (hW p hp).continuousAt).comp
      (f := fun p => slice p R z) (x := p) hmap.continuousAt).continuousWithinAt
  have hderiv (p : ℝ) (hp : p∈uIcc a b) : HasDerivAt v (d p) p := by
    have hp' : p∈Icc a b := by simpa only [uIcc_of_le hab] using hp
    have hU := slice_clock_derivative U p R z ((hu p hp').differentiableAt (by simp))
    have hV := slice_clock_derivative W p R z ((hW p hp').differentiableAt (by simp))
    apply (hU.mul hV).congr_deriv
    dsimp only [d,W]
    rw [mode_time_derivative r w hw outer _ hr hz]
    ring
  have hD : IntervalIntegrable d volume a b := hd.intervalIntegrable_of_Icc hab
  have hV : IntervalIntegrable v volume a b := hv.intervalIntegrable_of_Icc hab
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hD
  calc
    _ = ∫ p in a..b, d p+(2*w)*v p := by
      apply intervalIntegral.integral_congr
      intro p hp
      dsimp only [d,v,U,W]
      ring
    _ = (∫ p in a..b, d p)+(2*w)*(∫ p in a..b,v p) := by
      rw [intervalIntegral.integral_add hD (hV.const_mul (2*w)),intervalIntegral.integral_const_mul]
    _ = _ := by rw [hFTC]

private theorem top_integrable (U V : F) (hU : ExteriorSmooth U) (hV : ExteriorSmooth V)
    (p R Y : ℝ) (hp : 0<p) (hr : 1<R) (hy : 0<Y) :
    IntervalIntegrable (fun X => transfer U V 1 (slice p R (point X Y))) volume (-1/2:ℝ) (1/2:ℝ) := by
  apply Continuous.intervalIntegrable
  apply continuous_iff_continuousAt.mpr
  intro X
  have hs := smooth_partial hV 3 (slice p R (point X Y)) hp hr (by simpa [slice,point] using hy)
  have hu := hU (slice p R (point X Y)) hp hr (by simpa [slice,point] using hy)
  change ContinuousAt (fun X => U (slice p R (point X Y))*coordDeriv 3 V (slice p R (point X Y))) X
  exact (hu.continuousAt.mul hs.continuousAt).comp
    (f:=fun X => slice p R (point X Y)) (show Continuous (fun X : ℝ => slice p R (point X Y)) by
      unfold slice point; fun_prop).continuousAt

private theorem partial_scale_germ (U V : F) (c : ℂ) (x : P) (i : Fin 4)
    (hV : DifferentiableAt ℝ V x) (he : U =ᶠ[𝓝 x] fun z => c*V z) :
    coordDeriv i U x=c*coordDeriv i V x := by
  unfold coordDeriv
  rw [he.fderiv_eq (𝕜:=ℝ),fderiv_const_mul hV]
  simp only [smul_apply,smul_eq_mul]

private theorem mode_normal_contact (r : XiZeroCopy) (w : ℂ) (hw : w.im≠0) (outer : Bool)
    (x : P) (hr : 1<x 1) (hy : 0<x 3) :
    coordDeriv 3 (scalarContact (modeScalar r w outer)) x=
      (eigenvalue r-2)*coordDeriv 3 (modeScalar r w outer) x := by
  apply partial_scale_germ _ _ _ x 3 ((modeScalar_smooth r w hw outer x hr hy).differentiableAt (by simp))
  filter_upwards [(isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hr,
    (isOpen_lt continuous_const (continuous_apply 3)).mem_nhds hy] with z hz1 hz3
  exact mode_scalar_contact r w hw outer z hz1 hz3

private theorem mode_normal_time (r : XiZeroCopy) (w : ℂ) (hw : w.im≠0) (outer : Bool)
    (x : P) (hr : 1<x 1) (hy : 0<x 3) :
    coordDeriv 3 (coordDeriv 0 (modeScalar r w outer)) x=
      -w*coordDeriv 3 (modeScalar r w outer) x := by
  apply partial_scale_germ _ _ _ x 3 ((modeScalar_smooth r w hw outer x hr hy).differentiableAt (by simp))
  filter_upwards [(isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hr,
    (isOpen_lt continuous_const (continuous_apply 3)).mem_nhds hy] with z hz1 hz3
  exact mode_time_derivative r w hw outer z hz1 hz3

private theorem coordinate_line_diff (U : F) (x : P) (i : Fin 4)
    (hU : DifferentiableAt ℝ U x) :
    DifferentiableAt ℝ (fun a => U (Function.update x i a)) (x i) := by
  have hu : DifferentiableAt ℝ U (Function.update x i (x i)) := by
    simpa only [Function.update_eq_self] using hU
  exact hu.comp _ (hasDerivAt_update x i (x i)).differentiableAt

private theorem normal_orbit (V : F) (hV : ExteriorSmooth V) (x : P)
    (hp : 0<x 0) (hr : 1<x 1) (hy : 0<x 3) :
    coordDeriv 3 (orbitDerivative V 1) x=
      ((x 1:ℂ)^(2 : ℕ)-1)*coordDeriv 3 (coordDeriv 1 V) x+coordDeriv 3 (coordDeriv 0 V) x := by
  have h1 := (smooth_partial hV 1 x hp hr hy).differentiableAt (by simp)
  have h0 := (smooth_partial hV 0 x hp hr hy).differentiableAt (by simp)
  rw [coordinate_update _ x 3 ((orbit_smooth hV 1 x hp hr hy).differentiableAt (by simp))]
  have he : (fun a => orbitDerivative V 1 (Function.update x 3 a))=
      fun a => ((x 1:ℂ)^(2 : ℕ)-1)*coordDeriv 1 V (Function.update x 3 a)+
        coordDeriv 0 V (Function.update x 3 a) := by
    funext a
    simp only [orbitDerivative,one_ne_zero,ite_false,Function.update_of_ne (by decide : (1:Fin 4)≠3)]
  rw [he]
  change deriv ((fun a => ((x 1:ℂ)^(2 : ℕ)-1)*coordDeriv 1 V (Function.update x 3 a)) +
    fun a => coordDeriv 0 V (Function.update x 3 a)) (x 3) = _
  rw [deriv_add ((coordinate_line_diff _ x 3 h1).const_mul _)
    (coordinate_line_diff _ x 3 h0),deriv_const_mul _ (coordinate_line_diff _ x 3 h1),
    ← coordinate_update _ x 3 h1,← coordinate_update _ x 3 h0]

private def modeTopDensity (q r : XiZeroCopy) (branch outer : Bool) (amp w : ℂ)
    (j : Fin 2) (x : P) : ℂ :=
  let U := sourceScalar q branch amp
  let W := modeScalar r w outer
  let E := orbitDerivative W j
  transfer (orbitDerivative U j) (scalarContact W) 1 x-
    transfer (forcedContact q branch amp) E 1 x+
    eigenvalue r*(transfer E U 1 x-transfer U E 1 x)

private theorem modeTopDensity_integrable (q r : XiZeroCopy) (branch outer : Bool) (amp w : ℂ)
    (hw : w.im≠0) (j : Fin 2) (p R Y : ℝ) (hp : 0<p) (hr : 1<R) (hy : 0<Y) :
    IntervalIntegrable (fun X => modeTopDensity q r branch outer amp w j (slice p R (point X Y)))
      volume (-1/2:ℝ) (1/2:ℝ) := by
  have hU := source_smooth q branch amp
  have hW := mode_smooth r w hw outer
  exact ((top_integrable _ _ (orbit_smooth hU j) (contact_smooth hW) p R Y hp hr hy).sub
    (top_integrable _ _ (forced_smooth q branch amp) (orbit_smooth hW j) p R Y hp hr hy)).add
    (((top_integrable _ _ (orbit_smooth hW j) hU p R Y hp hr hy).sub
      (top_integrable _ _ hU (orbit_smooth hW j) p R Y hp hr hy)).const_mul (eigenvalue r))

private theorem modeCompleteTopFlux_integral (q r : XiZeroCopy) (branch outer : Bool) (amp w : ℂ)
    (hw : w.im≠0) (j : Fin 2) (p R Y : ℝ) (hp : 0<p) (hr : 1<R) (hy : 0<Y) :
    modeCompleteTopFlux q r branch outer amp w j p R Y=
      ∫ X in (-1/2:ℝ)..1/2,modeTopDensity q r branch outer amp w j (slice p R (point X Y)) := by
  have hU := source_smooth q branch amp
  have hW := mode_smooth r w hw outer
  have h1 := top_integrable _ _ (orbit_smooth hU j) (contact_smooth hW) p R Y hp hr hy
  have h2 := top_integrable _ _ (forced_smooth q branch amp) (orbit_smooth hW j) p R Y hp hr hy
  have h3 := top_integrable _ _ (orbit_smooth hW j) hU p R Y hp hr hy
  have h4 := top_integrable _ _ hU (orbit_smooth hW j) p R Y hp hr hy
  simp only [modeTopDensity,modeCompleteTopFlux,topFlux]
  rw [intervalIntegral.integral_add (h1.sub h2) ((h3.sub h4).const_mul (eigenvalue r)),
    intervalIntegral.integral_sub h1 h2,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub h3 h4]
  simp only [neg_div]

private theorem mode_static_top_density (q r : XiZeroCopy) (branch outer : Bool) (amp w : ℂ)
    (hw : w.im≠0) (x : P) (hp : 0<x 0) (hr : 1<x 1) (hy : 0<x 3) :
    let U := sourceScalar q branch amp
    let W := modeScalar r w outer
    let D := forcedContact q branch amp
    let f := (x 1:ℂ)^(2 : ℕ)-1
    let mu := eigenvalue r
    (modeTopDensity q r branch outer amp w 0 x-modeTopDensity q r branch outer amp w 1 x/f)/(x 1:ℂ)^(2 : ℕ)=
      (-(mu-2)*transfer (coordDeriv 0 U) W 1 x-w*transfer D W 1 x+
        mu*w*(transfer W U 1 x-transfer U W 1 x))/((x 1:ℂ)^(2 : ℕ)*f) := by
  dsimp only
  simp only [modeTopDensity,transfer,angularIndex,Matrix.cons_val]
  rw [mode_normal_contact r w hw outer x hr hy,
    normal_orbit _ (mode_smooth r w hw outer) x hp hr hy,
    mode_normal_time r w hw outer x hr hy]
  have hz : orbitDerivative (modeScalar r w outer) 0=coordDeriv 1 (modeScalar r w outer) := by
    funext z
    simp only [orbitDerivative,ite_true]
  rw [hz]
  simp only [orbitDerivative,ite_true,one_ne_zero,ite_false]
  rw [mode_time_derivative r w hw outer x hr hy]
  have hR : (x 1:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (by linarith)
  have hf : (x 1:ℂ)^(2 : ℕ)-1≠0 := by exact_mod_cast (show (x 1)^(2 : ℕ)-1≠0 by nlinarith)
  field_simp [hR,hf]
  ring


/-- The complete static cusp flux of the original metric family contains no
reader radius derivative. The full original source contact is retained. -/
theorem mode_static_top_flux (q r : XiZeroCopy) (branch outer : Bool) (amp w : ℂ)
    (hw : w.im≠0) (p R Y : ℝ) (hp : 0<p) (hr : 1<R) (hy : 0<Y) :
    let U := sourceScalar q branch amp
    let W := modeScalar r w outer
    let f := (R:ℂ)^(2 : ℕ)-1
    let mu := eigenvalue r
    (modeCompleteTopFlux q r branch outer amp w 0 p R Y-
      modeCompleteTopFlux q r branch outer amp w 1 p R Y/f)/(R:ℂ)^(2 : ℕ)=
      (-(mu-2)*topFlux (coordDeriv 0 U) W p R Y-
        w*topFlux (forcedContact q branch amp) W p R Y+
        mu*w*(topFlux W U p R Y-topFlux U W p R Y))/((R:ℂ)^(2 : ℕ)*f) := by
  dsimp only
  have hU := source_smooth q branch amp
  have hW := mode_smooth r w hw outer
  have h0 := modeTopDensity_integrable q r branch outer amp w hw 0 p R Y hp hr hy
  have h1 := modeTopDensity_integrable q r branch outer amp w hw 1 p R Y hp hr hy
  have ht := top_integrable _ _ (smooth_partial hU 0) hW p R Y hp hr hy
  have hd := top_integrable _ _ (forced_smooth q branch amp) hW p R Y hp hr hy
  have hwu := top_integrable _ _ hW hU p R Y hp hr hy
  have huw := top_integrable _ _ hU hW p R Y hp hr hy
  rw [modeCompleteTopFlux_integral q r branch outer amp w hw 0 p R Y hp hr hy,
    modeCompleteTopFlux_integral q r branch outer amp w hw 1 p R Y hp hr hy,
    ← intervalIntegral.integral_div,← intervalIntegral.integral_sub h0
      (h1.div_const ((R:ℂ)^(2 : ℕ)-1)),← intervalIntegral.integral_div]
  calc
    _ = ∫ X in (-1/2:ℝ)..1/2,
      (-(eigenvalue r-2)*transfer (coordDeriv 0 (sourceScalar q branch amp)) (modeScalar r w outer) 1 (slice p R (point X Y))-
        w*transfer (forcedContact q branch amp) (modeScalar r w outer) 1 (slice p R (point X Y))+
        eigenvalue r*w*(transfer (modeScalar r w outer) (sourceScalar q branch amp) 1 (slice p R (point X Y))-
          transfer (sourceScalar q branch amp) (modeScalar r w outer) 1 (slice p R (point X Y))))/((R:ℂ)^(2 : ℕ)*((R:ℂ)^(2 : ℕ)-1)) := by
      apply intervalIntegral.integral_congr
      intro X hX
      exact mode_static_top_density q r branch outer amp w hw (slice p R (point X Y)) hp hr (by simpa [slice,point] using hy)
    _ = _ := by
      rw [intervalIntegral.integral_div,
        intervalIntegral.integral_add ((ht.const_mul _).sub (hd.const_mul _)) ((hwu.sub huw).const_mul _),
        intervalIntegral.integral_sub (ht.const_mul _) (hd.const_mul _),
        intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul,intervalIntegral.integral_sub hwu huw]
      simp only [topFlux,neg_div]

private theorem top_rectangle_continuous (U V : F) (hU : ExteriorSmooth U) (hV : ExteriorSmooth V)
    (a b R Y : ℝ) (ha : 0<a) (hr : 1<R) (hy : 0<Y) :
    ContinuousOn (fun z : ℝ×ℝ => transfer U V 1 (slice z.1 R (point z.2 Y)))
      (Icc a b ×ˢ Icc (-1/2:ℝ) (1/2:ℝ)) := by
  intro z hz
  have hu := hU (slice z.1 R (point z.2 Y)) (ha.trans_le hz.1.1) hr (by simpa [slice,point] using hy)
  have hv := smooth_partial hV 3 (slice z.1 R (point z.2 Y)) (ha.trans_le hz.1.1) hr (by simpa [slice,point] using hy)
  change ContinuousWithinAt (fun z : ℝ×ℝ => U (slice z.1 R (point z.2 Y))*coordDeriv 3 V (slice z.1 R (point z.2 Y))) _ z
  exact ((hu.continuousAt.mul hv.continuousAt).comp
    (f:=fun z : ℝ×ℝ => slice z.1 R (point z.2 Y))
    (show Continuous (fun z : ℝ×ℝ => slice z.1 R (point z.2 Y)) by unfold slice point; fun_prop).continuousAt).continuousWithinAt

private theorem top_time_swap (U V : F) (hU : ExteriorSmooth U) (hV : ExteriorSmooth V)
    (a b R Y : ℝ) (ha : 0<a) (hab : a≤b) (hr : 1<R) (hy : 0<Y) :
    (∫ p in a..b, topFlux U V p R Y)=
      ∫ X in (-1/2:ℝ)..1/2, ∫ p in a..b, transfer U V 1 (slice p R (point X Y)) := by
  simp only [topFlux,← neg_div]
  apply MeasureTheory.intervalIntegral_intervalIntegral_swap
  rw [uIoc_of_le hab,uIoc_of_le (by norm_num : (-1/2:ℝ)≤1/2)]
  exact ((top_rectangle_continuous U V hU hV a b R Y ha hr hy).integrableOn_compact
    (isCompact_Icc.prod isCompact_Icc)).mono_set (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)

private theorem top_time_integrable (U V : F) (hU : ExteriorSmooth U) (hV : ExteriorSmooth V)
    (a b R Y : ℝ) (ha : 0<a) (hab : a≤b) (hr : 1<R) (hy : 0<Y) :
    IntervalIntegrable (fun p => topFlux U V p R Y) volume a b := by
  have hi : Integrable (fun z : ℝ×ℝ => transfer U V 1 (slice z.1 R (point z.2 Y)))
      ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc (-1/2:ℝ) (1/2:ℝ)))) := by
    rw [Measure.prod_restrict,← Measure.volume_eq_prod]
    exact ((top_rectangle_continuous U V hU hV a b R Y ha hr hy).integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)).mono_set (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  simpa only [topFlux,← neg_div,intervalIntegral.integral_of_le (by norm_num : (-1/2:ℝ)≤1/2),IntegrableOn]
    using hi.integral_prod_left

private theorem time_point_integrable (U V : F) (hU : ExteriorSmooth U) (hV : ExteriorSmooth V)
    (a b R Y X : ℝ) (ha : 0<a) (hab : a≤b) (hr : 1<R) (hy : 0<Y) :
    IntervalIntegrable (fun p => transfer U V 1 (slice p R (point X Y))) volume a b := by
  apply ContinuousOn.intervalIntegrable_of_Icc hab
  intro p hp
  have hu := hU (slice p R (point X Y)) (ha.trans_le hp.1) hr (by simpa [slice,point] using hy)
  have hv := smooth_partial hV 3 (slice p R (point X Y)) (ha.trans_le hp.1) hr (by simpa [slice,point] using hy)
  change ContinuousWithinAt (fun p => U (slice p R (point X Y))*coordDeriv 3 V (slice p R (point X Y))) _ p
  exact ((hu.continuousAt.mul hv.continuousAt).comp
    (f:=fun p : ℝ => slice p R (point X Y))
    (show Continuous (fun p : ℝ => slice p R (point X Y)) by unfold slice; fun_prop).continuousAt).continuousWithinAt

private theorem time_point_transfer (U : F) (hU : ExteriorSmooth U)
    (r : XiZeroCopy) (w : ℂ) (hw : w.im≠0) (outer : Bool)
    (a b R Y X : ℝ) (ha : 0<a) (hab : a≤b) (hr : 1<R) (hy : 0<Y) :
    let W := modeScalar r w outer
    (∫ p in a..b, transfer (coordDeriv 0 U) W 1 (slice p R (point X Y)))=
      transfer U W 1 (slice b R (point X Y))-transfer U W 1 (slice a R (point X Y))+
        w*(∫ p in a..b, transfer U W 1 (slice p R (point X Y))) := by
  dsimp only
  let W := modeScalar r w outer
  let v := fun p => transfer U W 1 (slice p R (point X Y))
  let d := fun p => transfer (coordDeriv 0 U) W 1 (slice p R (point X Y))-w*v p
  have hW := mode_smooth r w hw outer
  have hderiv (p : ℝ) (hp : p∈uIcc a b) : HasDerivAt v (d p) p := by
    have hp' : 0<p := ha.trans_le ((uIcc_of_le hab ▸ hp).1)
    have hz : 0<(slice p R (point X Y)) 3 := by simpa [slice,point] using hy
    have hU' := slice_clock_derivative U p R (point X Y) ((hU _ hp' hr hz).differentiableAt (by simp))
    have hV' := slice_clock_derivative (coordDeriv 3 W) p R (point X Y)
      ((smooth_partial hW 3 _ hp' hr hz).differentiableAt (by simp))
    have ht : coordDeriv 0 (coordDeriv 3 W) (slice p R (point X Y))=
        -w*coordDeriv 3 W (slice p R (point X Y)) :=
      (coordDeriv_comm ((hW _ hp' hr hz).of_le
        (show (2:ℕ∞ω)≤∞ from WithTop.coe_le_coe.mpr le_top)) 0 3).trans
        (mode_normal_time r w hw outer _ hr hz)
    apply (hU'.mul hV').congr_deriv
    dsimp only [d,v,transfer,angularIndex,Matrix.cons_val]
    rw [ht]
    ring
  have hv := time_point_integrable U W hU hW a b R Y X ha hab hr hy
  have hu := time_point_integrable (coordDeriv 0 U) W (smooth_partial hU 0) hW a b R Y X ha hab hr hy
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hu.sub (hv.const_mul w))
  change (∫ p in a..b,transfer (coordDeriv 0 U) W 1 (slice p R (point X Y)))=v b-v a+w*(∫ p in a..b,v p)
  dsimp only [d] at hFTC
  rw [intervalIntegral.integral_sub hu (hv.const_mul w),intervalIntegral.integral_const_mul] at hFTC
  linear_combination hFTC


private theorem top_time_inner_integrable (U V : F) (hU : ExteriorSmooth U) (hV : ExteriorSmooth V)
    (a b R Y : ℝ) (ha : 0<a) (hab : a≤b) (hr : 1<R) (hy : 0<Y) :
    IntervalIntegrable (fun X => ∫ p in a..b, transfer U V 1 (slice p R (point X Y)))
      volume (-1/2:ℝ) (1/2:ℝ) := by
  have hi : Integrable (fun z : ℝ×ℝ => transfer U V 1 (slice z.1 R (point z.2 Y)))
      ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc (-1/2:ℝ) (1/2:ℝ)))) := by
    rw [Measure.prod_restrict,← Measure.volume_eq_prod]
    exact ((top_rectangle_continuous U V hU hV a b R Y ha hr hy).integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)).mono_set (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (-1/2:ℝ)≤1/2)]
  simpa only [intervalIntegral.integral_of_le hab,IntegrableOn] using hi.integral_prod_right

private theorem top_time_transfer (U : F) (hU : ExteriorSmooth U)
    (r : XiZeroCopy) (w : ℂ) (hw : w.im≠0) (outer : Bool)
    (a b R Y : ℝ) (ha : 0<a) (hab : a≤b) (hr : 1<R) (hy : 0<Y) :
    let W := modeScalar r w outer
    (∫ p in a..b, topFlux (coordDeriv 0 U) W p R Y)=
      topFlux U W b R Y-topFlux U W a R Y+w*(∫ p in a..b,topFlux U W p R Y) := by
  dsimp only
  have hW := mode_smooth r w hw outer
  have hb := top_integrable U (modeScalar r w outer) hU hW b R Y (ha.trans_le hab) hr hy
  have ha' := top_integrable U (modeScalar r w outer) hU hW a R Y ha hr hy
  have hi := top_time_inner_integrable U (modeScalar r w outer) hU hW a b R Y ha hab hr hy
  rw [top_time_swap (coordDeriv 0 U) _ (smooth_partial hU 0) hW a b R Y ha hab hr hy]
  calc
    _ = ∫ X in (-1/2:ℝ)..1/2,
      transfer U (modeScalar r w outer) 1 (slice b R (point X Y))-
        transfer U (modeScalar r w outer) 1 (slice a R (point X Y))+
        w*(∫ p in a..b,transfer U (modeScalar r w outer) 1 (slice p R (point X Y))) := by
      apply intervalIntegral.integral_congr
      intro X hX
      exact time_point_transfer U hU r w hw outer a b R Y X ha hab hr hy
    _ = _ := by
      rw [intervalIntegral.integral_add (hb.sub ha') (hi.const_mul w),
        intervalIntegral.integral_sub hb ha',intervalIntegral.integral_const_mul,
        ← top_time_swap U _ hU hW a b R Y ha hab hr hy]
      simp only [topFlux,neg_div]

private theorem top_forced_decomposition (q r : XiZeroCopy) (branch outer : Bool) (amp w : ℂ)
    (hw : w.im≠0) (p R Y : ℝ) (hp : 0<p) (hr : 1<R) (hy : 0<Y) :
    let U := sourceScalar q branch amp
    let W := modeScalar r w outer
    topFlux (forcedContact q branch amp) W p R Y=
      topFlux (angularLap U) W p R Y-2*topFlux U W p R Y+
        (R:ℂ)^(3 : ℕ)/((R:ℂ)^(2 : ℕ)-1)*topFlux (originalForcing q branch amp) W p R Y := by
  dsimp only
  have hU := source_smooth q branch amp
  have hW := mode_smooth r w hw outer
  have hL := top_integrable _ _ (lap_smooth hU) hW p R Y hp hr hy
  have hu := top_integrable _ _ hU hW p R Y hp hr hy
  have hf := top_integrable _ _ (original_forcing_smooth q branch amp) hW p R Y hp hr hy
  simp only [topFlux,← neg_div]
  calc
    _ = ∫ X in (-1/2:ℝ)..1/2,
      transfer (angularLap (sourceScalar q branch amp)) (modeScalar r w outer) 1 (slice p R (point X Y))-
        2*transfer (sourceScalar q branch amp) (modeScalar r w outer) 1 (slice p R (point X Y))+
        (R:ℂ)^(3 : ℕ)/((R:ℂ)^(2 : ℕ)-1)*transfer (originalForcing q branch amp) (modeScalar r w outer) 1 (slice p R (point X Y)) := by
      apply intervalIntegral.integral_congr
      intro X hX
      simp only [transfer,forcedContact,slice,Matrix.cons_val]
      ring
    _ = _ := by
      rw [intervalIntegral.integral_add (hL.sub (hu.const_mul 2)) (hf.const_mul _),
        intervalIntegral.integral_sub hL (hu.const_mul 2),intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]

/-- Exact finite-time complete metric-boundary transfer for the original
causal source and independent-frequency physical left reader. Both original
endpoint values and the full forcing boundary flux survive. No cusp, horizon,
or infinite-time limit is taken in this identity. -/
theorem mode_complete_boundary_time_transfer (q r : XiZeroCopy) (branch outer : Bool) (amp w : ℂ)
    (hw : w.im≠0) (a b R Y : ℝ) (ha : 0<a) (hab : a≤b) (hr : 1<R) (hy : 0<Y) :
    let U := sourceScalar q branch amp
    let W := modeScalar r w outer
    let f := (R:ℂ)^(2 : ℕ)-1
    let mu := eigenvalue r
    let lam := mu-2
    (∫ p in a..b,
      (modeCompleteTopFlux q r branch outer amp w 0 p R Y-
        modeCompleteTopFlux q r branch outer amp w 1 p R Y/f)/(R:ℂ)^(2 : ℕ))=
      (-lam*(topFlux U W b R Y-topFlux U W a R Y)+
        w*(∫ p in a..b,mu*topFlux W U p R Y-topFlux (angularLap U) W p R Y-
          2*lam*topFlux U W p R Y-(R:ℂ)^(3 : ℕ)/f*topFlux (originalForcing q branch amp) W p R Y))/
        ((R:ℂ)^(2 : ℕ)*f) := by
  dsimp only
  let U := sourceScalar q branch amp
  let W := modeScalar r w outer
  let mu := eigenvalue r
  let f := (R:ℂ)^(2 : ℕ)-1
  have hU := source_smooth q branch amp
  have hW := mode_smooth r w hw outer
  have hu := top_time_integrable U W hU hW a b R Y ha hab hr hy
  have ht := top_time_integrable (coordDeriv 0 U) W (smooth_partial hU 0) hW a b R Y ha hab hr hy
  have hd := top_time_integrable (forcedContact q branch amp) W (forced_smooth q branch amp) hW a b R Y ha hab hr hy
  have hv := top_time_integrable W U hW hU a b R Y ha hab hr hy
  have hL := top_time_integrable (angularLap U) W (lap_smooth hU) hW a b R Y ha hab hr hy
  have hF := top_time_integrable (originalForcing q branch amp) W (original_forcing_smooth q branch amp) hW a b R Y ha hab hr hy
  have hD : (∫ p in a..b,topFlux (forcedContact q branch amp) W p R Y)=
      (∫ p in a..b,topFlux (angularLap U) W p R Y)-2*(∫ p in a..b,topFlux U W p R Y)+
        (R:ℂ)^(3 : ℕ)/f*(∫ p in a..b,topFlux (originalForcing q branch amp) W p R Y) := by
    calc
      _ = ∫ p in a..b,topFlux (angularLap U) W p R Y-2*topFlux U W p R Y+
        (R:ℂ)^(3 : ℕ)/f*topFlux (originalForcing q branch amp) W p R Y := by
        apply intervalIntegral.integral_congr
        intro p hp
        have hp' : p∈Icc a b := by simpa only [uIcc_of_le hab] using hp
        exact top_forced_decomposition q r branch outer amp w hw p R Y (ha.trans_le hp'.1) hr hy
      _ = _ := by
        rw [intervalIntegral.integral_add (hL.sub (hu.const_mul 2)) (hF.const_mul _),
          intervalIntegral.integral_sub hL (hu.const_mul 2),intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul]
  have hB : (∫ p in a..b,
      (modeCompleteTopFlux q r branch outer amp w 0 p R Y-
        modeCompleteTopFlux q r branch outer amp w 1 p R Y/f)/(R:ℂ)^(2 : ℕ))=
      (-(mu-2)*(∫ p in a..b,topFlux (coordDeriv 0 U) W p R Y)-
        w*(∫ p in a..b,topFlux (forcedContact q branch amp) W p R Y)+
        mu*w*((∫ p in a..b,topFlux W U p R Y)-(∫ p in a..b,topFlux U W p R Y)))/((R:ℂ)^(2 : ℕ)*f) := by
    calc
      _ = ∫ p in a..b, (-(mu-2)*topFlux (coordDeriv 0 U) W p R Y-
        w*topFlux (forcedContact q branch amp) W p R Y+
        mu*w*(topFlux W U p R Y-topFlux U W p R Y))/((R:ℂ)^(2 : ℕ)*f) := by
        apply intervalIntegral.integral_congr
        intro p hp
        have hp' : p∈Icc a b := by simpa only [uIcc_of_le hab] using hp
        exact mode_static_top_flux q r branch outer amp w hw p R Y (ha.trans_le hp'.1) hr hy
      _ = _ := by
        rw [intervalIntegral.integral_div,
          intervalIntegral.integral_add ((ht.const_mul _).sub (hd.const_mul _)) ((hv.sub hu).const_mul _),
          intervalIntegral.integral_sub (ht.const_mul _) (hd.const_mul _),
          intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul,intervalIntegral.integral_sub hv hu]
  change (∫ p in a..b,
      (modeCompleteTopFlux q r branch outer amp w 0 p R Y-
        modeCompleteTopFlux q r branch outer amp w 1 p R Y/f)/(R:ℂ)^(2 : ℕ))=
      (-(mu-2)*(topFlux U W b R Y-topFlux U W a R Y)+
        w*(∫ p in a..b,mu*topFlux W U p R Y-topFlux (angularLap U) W p R Y-
          2*(mu-2)*topFlux U W p R Y-(R:ℂ)^(3 : ℕ)/f*topFlux (originalForcing q branch amp) W p R Y))/((R:ℂ)^(2 : ℕ)*f)
  rw [hB,hD,top_time_transfer U hU r w hw outer a b R Y ha hab hr hy,
    intervalIntegral.integral_sub (((hv.const_mul mu).sub hL).sub (hu.const_mul _)) (hF.const_mul _),
    intervalIntegral.integral_sub ((hv.const_mul mu).sub hL) (hu.const_mul _),
    intervalIntegral.integral_sub (hv.const_mul mu) hL,
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul]
  ring

end
end RHTower.D4BMOriginalModularOrbit
