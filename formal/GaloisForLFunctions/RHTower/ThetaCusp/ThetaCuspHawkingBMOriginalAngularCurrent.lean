import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMActualIngoingCurrent
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMLeftQNMMetricEquation

/-!
# Original physical Einstein angular current

The angular components of the actual Einstein current are three bilinear
scalar Green transfers. Mixed derivatives commute on the original fields,
including the reconstructed source scalar U = R Z and the unchanged physical
left QNM. The final identity uses the original reconstructed metric current
and either original left radial normalization; no mode-admission or analytic
regularity premise is supplied.

The result is local in the exterior with positive ingoing time. It retains
all radial and temporal derivatives. Integration, boundary limits and
fixed-clock extinction are separate statements.
-/

open Set Filter Topology
open scoped ContDiff
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal
attribute [-instance] RCLike.innerProductSpace
namespace RHTower.D4BMOriginalAngularCurrent
open GaloisForLFunctions.HTGeometry ScalarTwoJet
private abbrev P4 := Fin 4 → ℝ
private abbrev F4 := P4 → ℂ

def angularIndex (j : Fin 2) : Fin 4 := ![2,3] j

def coexactField (F : F4) (j : Fin 2) (x : P4) : ℂ :=
  if j=0 then coordDeriv 3 F x else -coordDeriv 2 F x

def angularLap (F : F4) (x : P4) : ℂ :=
  (x 3:ℂ)^(2 : ℕ)*(coordDeriv 2 (coordDeriv 2 F) x+coordDeriv 3 (coordDeriv 3 F) x)

/-- Bilinear angular transfer formed from actual scalar fields and derivatives. -/
def greenPair (F G : F4) (j : Fin 2) (x : P4) : ℂ :=
  angularLap F x*coordDeriv (angularIndex j) G x-
    angularLap G x*coordDeriv (angularIndex j) F x

private theorem partial_neg (i : Fin 4) (F : F4) :
    coordDeriv i (fun x => -F x) = fun x => -coordDeriv i F x := by
  funext x
  simp [coordDeriv]

private theorem coexact_first {F : F4} {x : P4} (hF : ContDiffAt ℝ 2 F x)
    (i : Fin 4) (j : Fin 2) :
    coordDeriv i (coexactField F j) x=coexactField (coordDeriv i F) j x := by
  fin_cases j
  · change coordDeriv i (coordDeriv 3 F) x=coordDeriv 3 (coordDeriv i F) x
    exact coordDeriv_comm hF i 3
  · change coordDeriv i (fun y => -coordDeriv 2 F y) x= -coordDeriv 2 (coordDeriv i F) x
    rw [partial_neg]
    change -coordDeriv i (coordDeriv 2 F) x= -coordDeriv 2 (coordDeriv i F) x
    exact congrArg Neg.neg (coordDeriv_comm hF i 2)

private theorem coexact_curl {F : F4} {x : P4} (hF : ContDiffAt ℝ 3 F x) (i : Fin 4) :
    D4BMIngoingFullCurrent.curl (fun j => ofField (coexactField F j) x) i=
      -(coordDeriv 2 (coordDeriv 2 (coordDeriv i F)) x+
        coordDeriv 3 (coordDeriv 3 (coordDeriv i F)) x) := by
  have he (j : Fin 2) : coordDeriv i (coexactField F j) =ᶠ[𝓝 x]
      coexactField (coordDeriv i F) j := by
    filter_upwards [(hF.of_le (show (2:ℕ∞ω)≤3 by norm_num)).eventually (by norm_num)] with z hz
    exact coexact_first hz i j
  change coordDeriv 2 (coordDeriv i (coexactField F 1)) x-
    coordDeriv 3 (coordDeriv i (coexactField F 0)) x=_
  unfold coordDeriv
  rw [(he 1).fderiv_eq,(he 0).fderiv_eq]
  change coordDeriv 2 (coexactField (coordDeriv i F) 1) x-
    coordDeriv 3 (coexactField (coordDeriv i F) 0) x=_
  change coordDeriv 2 (fun y => -coordDeriv 2 (coordDeriv i F) y) x-
    coordDeriv 3 (coordDeriv 3 (coordDeriv i F)) x=_
  rw [partial_neg]
  ring

/-- The complete Einstein angular current is exactly three scalar Green transfers.
All fields are differentiated before the original current is evaluated. -/
theorem coexact_current (U W : F4) (x : P4)
    (hU : ContDiffAt ℝ 3 U x) (hW : ContDiffAt ℝ 3 W x) (j : Fin 2) :
    D4BMIngoingFullCurrent.current (x 1) (x 3)
      (fun a => ofField (coexactField U a) x) (fun a => ofField (coexactField W a) x)
      (angularIndex j)=
      1/(x 1:ℂ)^(2 : ℕ)*((((x 1:ℂ)^(2 : ℕ)-1)*greenPair (coordDeriv 1 U) (coordDeriv 1 W) j x)+
        greenPair (coordDeriv 1 U) (coordDeriv 0 W) j x+
        greenPair (coordDeriv 0 U) (coordDeriv 1 W) j x) := by
  have hU2 := hU.of_le (show (2:ℕ∞ω)≤3 by norm_num)
  have hW2 := hW.of_le (show (2:ℕ∞ω)≤3 by norm_num)
  have hD (F : F4) (hF : ContDiffAt ℝ 2 F x) (a : Fin 2) (i : Fin 4) :
      (ofField (coexactField F a) x).first i=coexactField (coordDeriv i F) a x :=
    coexact_first hF i a
  fin_cases j <;>
    simp [D4BMIngoingFullCurrent.current,angularIndex,
      D4BMIngoingFullCurrent.angularCurrent,hD U hU2,hD W hW2,
      coexact_curl hU,coexact_curl hW,coexactField,greenPair,angularLap]
  all_goals ring

/-- The actual scalar whose coexact derivative is the reconstructed original causal stream. -/
def sourceScalar (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (x : P4) : ℂ :=
  (x 1:ℂ)*D4BMActualIngoingCurrent.originalIngoingPotential q branch amp x

private theorem original_smooth (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (x : D4BMActualIngoingCurrent.HorizonPoint) (hr : 1<x.val 1) :
    ContDiffAt ℝ ∞ (D4BMActualIngoingCurrent.originalIngoingPotential q branch amp) x.val :=
  (D4BMActualIngoingCurrent.potential_smooth q branch amp x).congr_of_eventuallyEq
    (D4BMActualIngoingCurrent.potential_eq_original_germ q branch amp x hr).symm

private theorem radius_smooth : ContDiff ℝ ∞ (fun x : P4 => (x 1:ℂ)) :=
  Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ 1)

private theorem radius_partial (x : P4) (i : Fin 4) :
    coordDeriv i (fun z : P4 => (z 1:ℂ)) x=if i=1 then 1 else 0 := by
  have h := Complex.ofRealCLM.hasFDerivAt.comp x (hasFDerivAt_apply 1 x)
  change (fderiv ℝ (Complex.ofRealCLM ∘ (fun z : P4 => z 1)) x) (Pi.single i 1)=_
  rw [h.fderiv]
  by_cases hi : i=1
  · subst i; simp
  · simp [hi,Ne.symm hi]

/-- The reconstruction factor R remains in every derivative of the scalar source. -/
theorem sourceScalar_smooth (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (x : D4BMActualIngoingCurrent.HorizonPoint) (hr : 1<x.val 1) :
    ContDiffAt ℝ ∞ (sourceScalar q branch amp) x.val :=
  radius_smooth.contDiffAt.mul (original_smooth q branch amp x hr)

/-- Coexact reconstruction uses only differentiability of the actual potential. -/
theorem source_coexact (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (x : P4)
    (hZ : DifferentiableAt ℝ (D4BMActualIngoingCurrent.originalIngoingPotential q branch amp) x)
    (j : Fin 2) : coexactField (sourceScalar q branch amp) j x=
      D4BMActualIngoingCurrent.originalStream q branch amp j x := by
  have h (i : Fin 4) := coordDeriv_mul (radius_smooth.differentiable (by simp) x) hZ i
  fin_cases j
  · change coordDeriv 3 (fun z : P4 => (z 1:ℂ)*D4BMActualIngoingCurrent.originalIngoingPotential q branch amp z) x=_
    rw [h 3,radius_partial]
    simp [D4BMActualIngoingCurrent.originalStream,Fin.ext_iff]
  · change -coordDeriv 2 (fun z : P4 => (z 1:ℂ)*D4BMActualIngoingCurrent.originalIngoingPotential q branch amp z) x=_
    rw [h 2,radius_partial]
    simp [D4BMActualIngoingCurrent.originalStream,Fin.ext_iff]

/-- Coexact reconstruction agrees with the original source on an entire neighborhood. -/
theorem source_coexact_germ (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (x : D4BMActualIngoingCurrent.HorizonPoint) (hr : 1<x.val 1) (j : Fin 2) :
    coexactField (sourceScalar q branch amp) j =ᶠ[𝓝 x.val]
      D4BMActualIngoingCurrent.originalStream q branch amp j := by
  have hZ : ContDiffAt ℝ 1 (D4BMActualIngoingCurrent.originalIngoingPotential q branch amp) x.val :=
    (original_smooth q branch amp x hr).of_le (by simp)
  filter_upwards [hZ.eventually (by norm_num)] with z hz
  exact source_coexact q branch amp z (hz.differentiableAt (by norm_num)) j

/-- Equality on a neighborhood identifies every ordered derivative of the actual two-jet. -/
theorem ofField_germ {F G : F4} {x : P4} (he : F =ᶠ[𝓝 x] G) :
    ofField F x=ofField G x := by
  have hd (j : Fin 4) : coordDeriv j F =ᶠ[𝓝 x] coordDeriv j G := by
    filter_upwards [he.fderiv (𝕜 := ℝ)] with z hz
    exact congrArg (fun L => L (Pi.single j 1)) hz
  ext i j
  · exact he.self_of_nhds
  · change fderiv ℝ F x (Pi.single i 1)=fderiv ℝ G x (Pi.single i 1)
    rw [he.fderiv_eq]
  · change fderiv ℝ (coordDeriv j F) x (Pi.single i 1)=fderiv ℝ (coordDeriv j G) x (Pi.single i 1)
    rw [(hd j).fderiv_eq]

/-- Actual causal stream, with every ordered derivative and reconstruction factor retained. -/
theorem original_current (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (x : D4BMActualIngoingCurrent.HorizonPoint) (hr : 1<x.val 1)
    (W : F4) (hW : ContDiffAt ℝ 3 W x.val) (j : Fin 2) :
    D4BMIngoingFullCurrent.current (x.val 1) (x.val 3)
      (fun a => ofField (D4BMActualIngoingCurrent.originalStream q branch amp a) x.val)
      (fun a => ofField (coexactField W a) x.val) (angularIndex j)=
      1/(x.val 1:ℂ)^(2 : ℕ)*((((x.val 1:ℂ)^(2 : ℕ)-1)*
        greenPair (coordDeriv 1 (sourceScalar q branch amp)) (coordDeriv 1 W) j x.val)+
        greenPair (coordDeriv 1 (sourceScalar q branch amp)) (coordDeriv 0 W) j x.val+
        greenPair (coordDeriv 0 (sourceScalar q branch amp)) (coordDeriv 1 W) j x.val) := by
  have he (a : Fin 2) := ofField_germ (source_coexact_germ q branch amp x hr a)
  simp_rw [← he]
  exact coexact_current _ _ _ ((sourceScalar_smooth q branch amp x hr).of_le (show (3:ℕ∞ω)≤∞ from WithTop.coe_le_coe.mpr le_top)) hW j

private abbrev P2 := Fin 2 → ℝ
open D4BMPhysicalModeAction D4BMMetricReconstruction D4BMJointSource

private def timeRadius : P4 →L[ℝ] P2 :=
  ContinuousLinearMap.pi ![ContinuousLinearMap.proj 0,ContinuousLinearMap.proj 1]

/-- The unchanged original left radial mode, expressed in ingoing time. -/
def leftAmplitude (q : XiZeroCopy) (side outer : Bool) (z : P2) : ℂ :=
  Complex.exp (-D4BMLeftModeRadialEquation.frequency q side *
    ((z 0-D4BMIngoingCoordinates.tortoise (z 1)):ℂ))*
    radiusLift (D4BMLeftModeRadialEquation.profile q side outer) (z 1)

/-- Scalar generating the original left stream; both original radial normalizations remain. -/
def leftScalar (q : XiZeroCopy) (side outer : Bool) (x : P4) : ℂ :=
  leftAmplitude q side outer (timeRadius x)*
    D4BMLiteralCusp.scalar (physicalAngularParameter q) (angularPoint x)

/-- Pointwise formula for the original reader in the ingoing chart. -/
theorem leftScalar_value (q : XiZeroCopy) (side outer : Bool) (x : P4) :
    leftScalar q side outer x =
      Complex.exp (-D4BMLeftModeRadialEquation.frequency q side *
        ((x 0-D4BMIngoingCoordinates.tortoise (x 1)):ℂ))*
      radiusLift (D4BMLeftModeRadialEquation.profile q side outer) (x 1)*
      D4BMLiteralCusp.scalar (physicalAngularParameter q) (angularPoint x) := by
  simp [leftScalar,leftAmplitude,timeRadius]

private theorem angular_smooth : ContDiff ℝ ∞ angularPoint := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> exact contDiff_apply ℝ ℝ _

private theorem leftAmplitude_smooth (q : XiZeroCopy) (side outer : Bool) (z : P2)
    (hr : 1<z 1) : ContDiffAt ℝ ∞ (leftAmplitude q side outer) z := by
  have htneg : D4BMIngoingCoordinates.tortoise (z 1)<0 := by
    have h := Real.log_lt_log (show 0<z 1-1 by linarith) (show z 1-1<z 1+1 by linarith)
    dsimp [D4BMIngoingCoordinates.tortoise]
    linarith
  have ht : ContDiffAt ℝ ∞ D4BMIngoingCoordinates.tortoise (z 1) := by
    have hm : z 1-1≠0 := by linarith
    have hp : z 1+1≠0 := by linarith
    unfold D4BMIngoingCoordinates.tortoise
    fun_prop
  have htR := ht.comp z (contDiff_apply ℝ ℝ (1:Fin 2)).contDiffAt
  have hP := (D4BMLeftModeRadialEquation.profile_smooth q side outer).contDiffAt
    (isOpen_Iio.mem_nhds htneg)
  have hR : ContDiffAt ℝ ∞ (fun y : P2 => (y 1:ℂ)) z :=
    (Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ (1:Fin 2))).contDiffAt
  have hE : ContDiffAt ℝ ∞ (fun y : P2 => Complex.exp
      (-D4BMLeftModeRadialEquation.frequency q side*((y 0-D4BMIngoingCoordinates.tortoise (y 1)):ℂ))) z :=
    by
      have hc := Complex.ofRealCLM.contDiff.contDiffAt.comp z
        ((contDiff_apply ℝ ℝ (0:Fin 2)).contDiffAt.sub htR)
      simpa [Function.comp_def] using
        (contDiffAt_const (c := -D4BMLeftModeRadialEquation.frequency q side) |>.mul hc).cexp
  have h := hE.mul (hR.mul (hP.comp z htR))
  exact h

/-- All actual spacetime derivatives of the original left scalar exist in the exterior. -/
theorem leftScalar_smooth (q : XiZeroCopy) (side outer : Bool) (x : P4)
    (hr : 1<x 1) (hy : 0<x 3) : ContDiffAt ℝ ∞ (leftScalar q side outer) x := by
  have hA := (leftAmplitude_smooth q side outer (timeRadius x) hr).comp x timeRadius.contDiff.contDiffAt
  have hS : ContDiffAt ℝ ∞ (D4BMLiteralCusp.scalar (physicalAngularParameter q)) (angularPoint x) :=
    (D4BMAngularSeries.cuspLeg_contDiffOn .scalar (physicalAngularParameter q)).contDiffAt
      ((isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hy)
  exact hA.mul (hS.comp x angular_smooth.contDiffAt)

private theorem timeRadius_angular_partial (F : P2 → ℂ) (x : P4)
    (hF : DifferentiableAt ℝ F (timeRadius x)) (j : Fin 2) :
    coordDeriv (angularIndex j) (F ∘ timeRadius) x=0 := by
  have h := hF.hasFDerivAt.comp x timeRadius.hasFDerivAt
  have hb : timeRadius (Pi.single (angularIndex j) 1)=0 := by
    fin_cases j <;> ext i <;> fin_cases i <;> simp [timeRadius,angularIndex,Fin.ext_iff]
  change fderiv ℝ (F ∘ timeRadius) x (Pi.single (angularIndex j) 1)=0
  rw [h.fderiv,ContinuousLinearMap.comp_apply,hb,map_zero]

private theorem left_coexact (q : XiZeroCopy) (side outer : Bool) (x : P4)
    (hr : 1<x 1) (hy : 0<x 3) (j : Fin 2) :
    coexactField (leftScalar q side outer) j x=
      leftAmplitude q side outer (timeRadius x)*
        D4BMLiteralCusp.vector (physicalAngularParameter q) j (angularPoint x) := by
  let A := leftAmplitude q side outer
  let S := D4BMLiteralCusp.scalar (physicalAngularParameter q)
  have hA : DifferentiableAt ℝ A (timeRadius x) :=
    (leftAmplitude_smooth q side outer (timeRadius x) hr).differentiableAt (by simp)
  have hS : ContDiffAt ℝ 2 S (angularPoint x) :=
    D4BMLiteralCusp.scalar_contDiffAt (physicalAngularParameter q) 2 (angularPoint x) hy
  have hSL : DifferentiableAt ℝ (fun y => S (angularPoint y)) x :=
    (hS.differentiableAt (by norm_num)).comp x (angular_smooth.differentiable (by simp) x)
  have hjet := D4BMScalarLinearEquation.angular_lift_jet S x hS
  have hpartial (a : Fin 2) : coordDeriv (angularIndex a) (leftScalar q side outer) x=
      A (timeRadius x)*coordDeriv a S (angularPoint x) := by
    change coordDeriv (angularIndex a) (fun y => (A ∘ timeRadius) y*S (angularPoint y)) x=_
    rw [coordDeriv_mul (hA.comp x timeRadius.differentiableAt) hSL,
      timeRadius_angular_partial A x hA,zero_mul,zero_add]
    have hJ := congrArg (fun J : ScalarTwoJet (Fin 4) ℂ => J.first (angularIndex a)) hjet
    change coordDeriv (angularIndex a) (fun y => S (angularPoint y)) x=_ at hJ
    rw [hJ]
    fin_cases a <;> rfl
  fin_cases j
  · change coordDeriv (angularIndex 1) (leftScalar q side outer) x=_
    rw [hpartial 1]
    rfl
  · change -coordDeriv (angularIndex 0) (leftScalar q side outer) x=_
    rw [hpartial 0]
    change -(A (timeRadius x)*coordDeriv 0 S (angularPoint x))=
      A (timeRadius x)*(-coordDeriv 0 S (angularPoint x))
    ring

/-- The original physical left field in the ingoing chart, with no admission premise. -/
def leftStream (q : XiZeroCopy) (side outer : Bool) (j : Fin 2) (x : P4) : ℂ :=
  physicalLeftModeStream q (D4BMLeftModeRadialEquation.frequency q side) outer j
    ![x 0-D4BMIngoingCoordinates.tortoise (x 1),x 1,x 2,x 3]

/-- The original left field has its coexact scalar germ throughout the exterior. -/
theorem left_coexact_germ (q : XiZeroCopy) (side outer : Bool) (x : P4)
    (hr : 1<x 1) (hy : 0<x 3) (j : Fin 2) :
    coexactField (leftScalar q side outer) j =ᶠ[𝓝 x] leftStream q side outer j := by
  filter_upwards [(isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hr,
    (isOpen_lt continuous_const (continuous_apply 3)).mem_nhds hy] with z hzR hzY
  simpa [leftStream,leftAmplitude,physicalLeftModeStream,
    D4BMLeftModeRadialEquation.profile,timeRadius,angularPoint] using
    left_coexact q side outer z hzR hzY j

/-- The unchanged physical left stream has actual two-jet regularity for every R > 1. -/
theorem leftStream_smooth (q : XiZeroCopy) (side outer : Bool) (x : P4)
    (hr : 1<x 1) (hy : 0<x 3) (j : Fin 2) :
    ContDiffAt ℝ 2 (leftStream q side outer j) x := by
  have h : ContDiffAt ℝ 3 (leftScalar q side outer) x :=
    (leftScalar_smooth q side outer x hr hy).of_le (WithTop.coe_le_coe.mpr le_top)
  have hc : ContDiffAt ℝ 2 (coexactField (leftScalar q side outer) j) x := by
    fin_cases j
    · change ContDiffAt ℝ 2 (coordDeriv 3 (leftScalar q side outer)) x
      exact coordDeriv_contDiffAt h (by norm_num) 3
    · change ContDiffAt ℝ 2 (fun z => -coordDeriv 2 (leftScalar q side outer) z) x
      exact (coordDeriv_contDiffAt h (by norm_num) 2).neg
  exact hc.congr_of_eventuallyEq (left_coexact_germ q side outer x hr hy j).symm

/-- Substitution back to static coordinates recovers the unchanged physical test field. -/
theorem leftStream_static (q : XiZeroCopy) (side outer : Bool) (j : Fin 2) :
    (fun x => leftStream q side outer j (D4BMActualIngoingCurrent.ingoingPoint x))=
      physicalLeftModeStream q (D4BMLeftModeRadialEquation.frequency q side) outer j := by
  funext x
  have he : ![(D4BMActualIngoingCurrent.ingoingPoint x) 0-
      D4BMIngoingCoordinates.tortoise ((D4BMActualIngoingCurrent.ingoingPoint x) 1),
      (D4BMActualIngoingCurrent.ingoingPoint x) 1,
      (D4BMActualIngoingCurrent.ingoingPoint x) 2,
      (D4BMActualIngoingCurrent.ingoingPoint x) 3]=x := by
    ext i
    fin_cases i <;> simp [D4BMActualIngoingCurrent.ingoingPoint]
  change physicalLeftModeStream _ _ _ _ _=_
  rw [he]


/-- Actual original causal source paired against either unchanged physical left mode. -/
theorem original_physical_current (q r : XiZeroCopy) (branch side outer : Bool) (amp : ℂ)
    (x : D4BMActualIngoingCurrent.HorizonPoint) (hr : 1<x.val 1) (j : Fin 2) :
    D4BMIngoingFullCurrent.current (x.val 1) (x.val 3)
      (fun a => ofField (D4BMActualIngoingCurrent.originalStream q branch amp a) x.val)
      (fun a => ofField (leftStream r side outer a) x.val) (angularIndex j)=
      1/(x.val 1:ℂ)^(2 : ℕ)*((((x.val 1:ℂ)^(2 : ℕ)-1)*
        greenPair (coordDeriv 1 (sourceScalar q branch amp))
          (coordDeriv 1 (leftScalar r side outer)) j x.val)+
        greenPair (coordDeriv 1 (sourceScalar q branch amp))
          (coordDeriv 0 (leftScalar r side outer)) j x.val+
        greenPair (coordDeriv 0 (sourceScalar q branch amp))
          (coordDeriv 1 (leftScalar r side outer)) j x.val) := by
  have he (a : Fin 2) := ofField_germ (left_coexact_germ r side outer x.val hr x.property.2.2.2 a)
  simp_rw [← he]
  exact original_current q branch amp x hr _
    ((leftScalar_smooth r side outer x.val hr x.property.2.2.2).of_le
      (show (3:ℕ∞ω)≤∞ from WithTop.coe_le_coe.mpr le_top)) j

/-- The same decomposition for the Einstein current of the reconstructed metric,
with the literal physical static left field, evaluated before differentiation. -/
theorem original_physical_metric_current (q r : XiZeroCopy)
    (branch side outer : Bool) (amp : ℂ) (x : D4BMBackground.ExteriorPoint)
    (hp : 0<D4BMActualIngoingCurrent.ingoingPoint x.val 0) (hR : x.val 1<3) (j : Fin 2) :
    D4BMActualIngoingCurrent.metricIngoingCurrent x
      (D4BMActualIngoingCurrent.originalStaticStream q branch amp)
      (physicalLeftModeStream r (D4BMLeftModeRadialEquation.frequency r side) outer)
        (angularIndex j)=
      1/(x.val 1:ℂ)^(2 : ℕ)*((((x.val 1:ℂ)^(2 : ℕ)-1)*
        greenPair (coordDeriv 1 (sourceScalar q branch amp))
          (coordDeriv 1 (leftScalar r side outer)) j (D4BMActualIngoingCurrent.ingoingPoint x.val))+
        greenPair (coordDeriv 1 (sourceScalar q branch amp))
          (coordDeriv 0 (leftScalar r side outer)) j (D4BMActualIngoingCurrent.ingoingPoint x.val)+
        greenPair (coordDeriv 0 (sourceScalar q branch amp))
          (coordDeriv 1 (leftScalar r side outer)) j (D4BMActualIngoingCurrent.ingoingPoint x.val)) := by
  let y : D4BMActualIngoingCurrent.HorizonPoint :=
    ⟨D4BMActualIngoingCurrent.ingoingPoint x.val,hp,
      (show (1/3:ℝ)<x.val 1 by linarith [x.property.1]),hR,x.property.2⟩
  have hQ (a : Fin 2) : ContDiffAt ℝ 2 (leftStream r side outer a) y.val :=
    leftStream_smooth r side outer y.val x.property.1 x.property.2 a
  have h := D4BMActualIngoingCurrent.original_causal_metric_current q branch amp x hp hR
    (leftStream r side outer) hQ
  have he : (fun a z => leftStream r side outer a (D4BMActualIngoingCurrent.ingoingPoint z))=
      physicalLeftModeStream r (D4BMLeftModeRadialEquation.frequency r side) outer :=
    funext (leftStream_static r side outer)
  rw [he] at h
  rw [h]
  exact original_physical_current q r branch side outer amp y x.property.1 j

end RHTower.D4BMOriginalAngularCurrent
