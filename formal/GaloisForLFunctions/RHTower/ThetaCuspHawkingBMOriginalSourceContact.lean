import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalGreenBoundary

/-!
# Complete original causal source contact in physical ingoing coordinates

The actual original null wave equation is transported through the unchanged tortoise and
angular-height coordinates. Radius reconstruction gives the scalar contact and its complete
coexact Einstein contact, including the original forcing and onset lift. All regularity is
produced for the original fields on the positive-time physical exterior. No radial moment
is divided out. Integrated normal-flux admission and the prescribed temporal/horizon/QNM
cutoff comparison remain separate obligations.
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
namespace RHTower.D4BMOriginalSourceContact
open GaloisForLFunctions.HTGeometry ScalarTwoJet
open D4BMIngoingCoordinates D4BMOriginalAngularCurrent
private abbrev P := Fin 4 → ℝ
private abbrev F := P → ℂ

private def chart (x : P) : P :=
  ![x 0,x 0-2*tortoise (x 1),x 2,Real.log (x 3)]

private def chartDifferential (x : P) : P →L[ℝ] P :=
  ContinuousLinearMap.pi ![ContinuousLinearMap.proj 0,
    ContinuousLinearMap.proj 0-(2/(x 1^(2 : ℕ)-1)) • ContinuousLinearMap.proj 1,
    ContinuousLinearMap.proj 2,(x 3)⁻¹ • ContinuousLinearMap.proj 3]

private theorem chart_hasFDerivAt (x : P) (hr : 1<x 1) (hy : 0<x 3) :
    HasFDerivAt chart (chartDifferential x) x := by
  have ht := (tortoise_hasDerivAt (x 1) hr).comp_hasFDerivAt (𝕜 := ℝ) (𝕜' := ℝ) x
    (hasFDerivAt_apply 1 x)
  have hl := (Real.hasDerivAt_log hy.ne').comp_hasFDerivAt (𝕜 := ℝ) (𝕜' := ℝ) x
    (hasFDerivAt_apply 3 x)
  apply hasFDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact hasFDerivAt_apply 0 x
  · convert! (hasFDerivAt_apply 0 x).sub (ht.const_mul 2) using 1
    ext v
    simp [div_eq_mul_inv,mul_assoc]
  · exact hasFDerivAt_apply 2 x
  · simpa [chartDifferential] using! hl

private theorem chart_basis (x : P) (i : Fin 4) :
    chartDifferential x (Pi.single i 1) =
      ![Pi.single 0 1+Pi.single 1 1,(-2/(x 1^(2 : ℕ)-1)) • Pi.single 1 1,
        Pi.single 2 1,(x 3)⁻¹ • Pi.single 3 1] i := by
  ext j
  fin_cases i <;> fin_cases j <;> simp [chartDifferential,neg_div]

private def pullFirst (f : F) (i : Fin 4) (x : P) : ℂ :=
  ![coordDeriv 0 f (chart x)+coordDeriv 1 f (chart x),
    (-2/((x 1:ℂ)^(2 : ℕ)-1))*coordDeriv 1 f (chart x),
    coordDeriv 2 f (chart x),(x 3:ℂ)⁻¹*coordDeriv 3 f (chart x)] i

private theorem chart_first {f : F} {x : P} (hr : 1<x 1) (hy : 0<x 3)
    (hf : DifferentiableAt ℝ f (chart x)) (i : Fin 4) :
    coordDeriv i (fun z => f (chart z)) x=pullFirst f i x := by
  change (fderiv ℝ (f ∘ chart) x) (Pi.single i 1)=_
  rw [(hf.hasFDerivAt.comp x (chart_hasFDerivAt x hr hy)).fderiv,
    ContinuousLinearMap.comp_apply,chart_basis]
  fin_cases i <;> simp [pullFirst,coordDeriv,Complex.real_smul]

private theorem chart_first_germ {f : F} {x : P} (hr : 1<x 1) (hy : 0<x 3)
    (hf : ContDiffAt ℝ 2 f (chart x)) (i : Fin 4) :
    coordDeriv i (fun z => f (chart z)) =ᶠ[𝓝 x] pullFirst f i := by
  have he := (chart_hasFDerivAt x hr hy).continuousAt.tendsto.eventually
    (hf.eventually (by norm_num))
  filter_upwards [he,(isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hr,
    (isOpen_lt continuous_const (continuous_apply 3)).mem_nhds hy] with z hz hzr hzy
  exact chart_first hzr hzy (hz.differentiableAt (by norm_num)) i

private theorem chart_partial_differentiable {f : F} {x : P}
    (hr : 1<x 1) (hy : 0<x 3) (hf : ContDiffAt ℝ 2 f (chart x)) (i : Fin 4) :
    DifferentiableAt ℝ (fun z => coordDeriv i f (chart z)) x :=
  ((coordDeriv_hasFDerivAt hf i).comp x (chart_hasFDerivAt x hr hy)).differentiableAt

private def radialMultiplier (x : P) : ℂ := -2/((x 1:ℂ)^(2 : ℕ)-1)
private def heightMultiplier (x : P) : ℂ := (x 3:ℂ)⁻¹

private theorem radialMultiplier_hasFDerivAt (x : P) (hr : 1<x 1) :
    HasFDerivAt radialMultiplier
      ((4*(x 1:ℂ)/((x 1:ℂ)^(2 : ℕ)-1)^(2 : ℕ)) •
        (Complex.ofRealCLM.comp (ContinuousLinearMap.proj 1))) x := by
  have hf : (x 1:ℂ)^(2 : ℕ)-1≠0 := by exact_mod_cast (show x 1^(2 : ℕ)-1≠0 by nlinarith)
  have hR := (hasDerivAt_id (x 1)).ofReal_comp
  have hd : HasDerivAt (fun r : ℝ => -2/((r:ℂ)^(2 : ℕ)-1))
      (4*(x 1:ℂ)/((x 1:ℂ)^(2 : ℕ)-1)^(2 : ℕ)) (x 1) := by
    convert! (hasDerivAt_const (x 1) (-2:ℂ)).div ((hR.pow 2).sub_const 1) hf using 1
    simp only [id_eq,Complex.ofReal_one,Pi.pow_apply]
    ring
  have hout : HasFDerivAt (fun r : ℝ => -2/((r:ℂ)^(2 : ℕ)-1))
      ((1:ℝ →L[ℝ] ℝ).smulRight (4*(x 1:ℂ)/((x 1:ℂ)^(2 : ℕ)-1)^(2 : ℕ))) (x 1) := hd.hasFDerivAt
  have hcoord : HasFDerivAt (fun z : P => z 1)
      (ContinuousLinearMap.proj 1 : P →L[ℝ] ℝ) x := hasFDerivAt_apply 1 x
  have hcomp := hout.comp x hcoord
  convert! hcomp using 1
  ext v
  simp [Complex.real_smul,mul_comm]

private theorem heightMultiplier_hasFDerivAt (x : P) (hy : 0<x 3) :
    HasFDerivAt heightMultiplier
      ((-(x 3:ℂ)⁻¹^(2 : ℕ)) • (Complex.ofRealCLM.comp (ContinuousLinearMap.proj 3))) x := by
  have hd := ((hasDerivAt_id (x 3)).ofReal_comp).inv (Complex.ofReal_ne_zero.mpr hy.ne')
  have hd' : HasDerivAt (fun r : ℝ => (r:ℂ)⁻¹) (-(x 3:ℂ)⁻¹^(2 : ℕ)) (x 3) := by
    convert! hd using 1
    simp [div_eq_mul_inv]
  have hout : HasFDerivAt (fun r : ℝ => (r:ℂ)⁻¹)
      ((1:ℝ →L[ℝ] ℝ).smulRight (-(x 3:ℂ)⁻¹^(2 : ℕ))) (x 3) := hd'.hasFDerivAt
  have hcoord : HasFDerivAt (fun z : P => z 3)
      (ContinuousLinearMap.proj 3 : P →L[ℝ] ℝ) x := hasFDerivAt_apply 3 x
  have hcomp := hout.comp x hcoord
  convert! hcomp using 1
  ext v
  simp [Complex.real_smul,mul_comm]

private theorem radialMultiplier_partial (x : P) (hr : 1<x 1) (i : Fin 4) :
    coordDeriv i radialMultiplier x=
      if i=1 then 4*(x 1:ℂ)/((x 1:ℂ)^(2 : ℕ)-1)^(2 : ℕ) else 0 := by
  rw [coordDeriv,(radialMultiplier_hasFDerivAt x hr).fderiv]
  by_cases hi : i=1
  · subst i; simp
  · simp [hi,Ne.symm hi]

private theorem heightMultiplier_partial (x : P) (hy : 0<x 3) (i : Fin 4) :
    coordDeriv i heightMultiplier x=if i=3 then -(x 3:ℂ)⁻¹^(2 : ℕ) else 0 := by
  rw [coordDeriv,(heightMultiplier_hasFDerivAt x hy).fderiv]
  by_cases hi : i=3
  · subst i; simp
  · simp [hi,Ne.symm hi]

private theorem chart_radial_second {f : F} {x : P} (hr : 1<x 1) (hy : 0<x 3)
    (hf : ContDiffAt ℝ 2 f (chart x)) (i : Fin 4) :
    coordDeriv i (coordDeriv 1 (fun z => f (chart z))) x=
      (if i=1 then 4*(x 1:ℂ)/((x 1:ℂ)^(2 : ℕ)-1)^(2 : ℕ) else 0)*coordDeriv 1 f (chart x)+
      radialMultiplier x*pullFirst (coordDeriv 1 f) i x := by
  have he := chart_first_germ hr hy hf 1
  change coordDeriv 1 (fun z => f (chart z)) =ᶠ[𝓝 x]
    (fun z => radialMultiplier z*coordDeriv 1 f (chart z)) at he
  rw [coordDeriv,he.fderiv_eq]
  change coordDeriv i (fun z => radialMultiplier z*coordDeriv 1 f (chart z)) x=_
  rw [coordDeriv_mul (radialMultiplier_hasFDerivAt x hr).differentiableAt
    (chart_partial_differentiable hr hy hf 1),radialMultiplier_partial x hr,
    chart_first hr hy (coordDeriv_hasFDerivAt hf 1).differentiableAt]

private theorem chart_horizontal_second {f : F} {x : P} (hr : 1<x 1) (hy : 0<x 3)
    (hf : ContDiffAt ℝ 2 f (chart x)) :
    coordDeriv 2 (coordDeriv 2 (fun z => f (chart z))) x=
      coordDeriv 2 (coordDeriv 2 f) (chart x) := by
  have he := chart_first_germ hr hy hf 2
  change coordDeriv 2 (fun z => f (chart z)) =ᶠ[𝓝 x]
    (fun z => coordDeriv 2 f (chart z)) at he
  rw [coordDeriv,he.fderiv_eq]
  exact chart_first hr hy (coordDeriv_hasFDerivAt hf 2).differentiableAt 2

private theorem chart_height_second {f : F} {x : P} (hr : 1<x 1) (hy : 0<x 3)
    (hf : ContDiffAt ℝ 2 f (chart x)) :
    coordDeriv 3 (coordDeriv 3 (fun z => f (chart z))) x=
      (x 3:ℂ)⁻¹^(2 : ℕ)*(coordDeriv 3 (coordDeriv 3 f) (chart x)-coordDeriv 3 f (chart x)) := by
  have he := chart_first_germ hr hy hf 3
  change coordDeriv 3 (fun z => f (chart z)) =ᶠ[𝓝 x]
    (fun z => heightMultiplier z*coordDeriv 3 f (chart z)) at he
  rw [coordDeriv,he.fderiv_eq]
  change coordDeriv 3 (fun z => heightMultiplier z*coordDeriv 3 f (chart z)) x=_
  rw [coordDeriv_mul (heightMultiplier_hasFDerivAt x hy).differentiableAt
    (chart_partial_differentiable hr hy hf 3),heightMultiplier_partial x hy,
    chart_first hr hy (coordDeriv_hasFDerivAt hf 3).differentiableAt]
  simp [pullFirst,heightMultiplier]
  ring

private def sliceFirst (f : F) (i : Fin 4) (x : P) : ℂ :=
  deriv (fun t => f (Function.update x i t)) (x i)

private theorem slice_first {f : F} {x : P} (hf : DifferentiableAt ℝ f x) (i : Fin 4) :
    sliceFirst f i x=coordDeriv i f x := by
  have hi : HasDerivAt (fun t : ℝ => Function.update x i t) (Pi.single i 1) (x i) := by
    apply hasDerivAt_pi.mpr
    intro j
    by_cases h : j=i
    · subst j; simpa using! hasDerivAt_id (x i)
    · simpa [h] using! hasDerivAt_const (x i) (x j)
  have hF : HasFDerivAt f (fderiv ℝ f x) (Function.update x i (x i)) := by
    simpa only [Function.update_eq_self] using hf.hasFDerivAt
  exact (hF.comp_hasDerivAt (x i) hi).deriv

private theorem slice_second {f : F} {x : P} (hf : ContDiffAt ℝ 2 f x) (i j : Fin 4) :
    sliceFirst (fun z => sliceFirst f j z) i x=coordDeriv i (coordDeriv j f) x := by
  have he : (fun z => sliceFirst f j z) =ᶠ[𝓝 x] coordDeriv j f := by
    filter_upwards [hf.eventually (by norm_num)] with z hz
    exact slice_first (hz.differentiableAt (by norm_num)) j
  have hc : ContinuousAt (fun t : ℝ => Function.update x i t) (x i) := by fun_prop
  have hg : (fun t => sliceFirst f j (Function.update x i t)) =ᶠ[𝓝 (x i)]
      (fun t => coordDeriv j f (Function.update x i t)) := hc.tendsto.eventually (show (fun z => sliceFirst f j z) =ᶠ[𝓝 (Function.update x i (x i))]
    coordDeriv j f by simpa using he)
  change deriv (fun t => sliceFirst f j (Function.update x i t)) (x i)=_
  rw [hg.deriv_eq]
  exact slice_first (coordDeriv_hasFDerivAt hf j).differentiableAt i

private def nativeField (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (x : P) : ℂ :=
  D4BMOriginalCausalPotential.originalPotential q branch amp (x 0) (x 1) (x 2) (x 3)

private def nativeLap (f : F) (x : P) : ℂ :=
  (Real.exp (x 3):ℂ)^(2 : ℕ)*coordDeriv 2 (coordDeriv 2 f) x+
    coordDeriv 3 (coordDeriv 3 f) x-coordDeriv 3 f x

private theorem native_wave (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (x : P) (hp : 0<x 0) (hpr : x 0<x 1) :
    4*coordDeriv 0 (coordDeriv 1 (nativeField q branch amp)) x-
      nativeLap (nativeField q branch amp) x/(Real.cosh ((x 0-x 1)/2):ℂ)^(2 : ℕ)=
      D4BMJointSource.timeOriginalForcing q branch amp
        ((x 0+x 1)/2) ((x 0-x 1)/2) ![x 2,Real.exp (x 3)] := by
  have hs := D4BMOriginalSpacetimeRegularity.originalPotential_smooth q branch amp x hp hpr
  have hs2 : ContDiffAt ℝ 2 (nativeField q branch amp) x := hs.of_le (WithTop.coe_le_coe.mpr le_top)
  have h := D4BMOriginalCausalPotential.originalPotential_wave q branch amp hp hpr.le (x 2) (x 3)
  rw [coordDeriv_comm hs2 0 1]
  rw [← slice_second hs2 1 0]
  unfold nativeLap
  rw [← slice_second hs2 2 2,← slice_second hs2 3 3,
    ← slice_first (hs2.differentiableAt (by norm_num)) 3]
  simpa [sliceFirst,nativeField,D4BMOriginalCausalPotential.angularLaplacian] using h

private theorem tortoise_neg (R : ℝ) (hr : 1<R) : tortoise R<0 := by
  have h := Real.log_lt_log (show 0<R-1 by linarith) (show R-1<R+1 by linarith)
  dsimp [tortoise]
  linarith

private theorem tortoise_cosh_weight (R : ℝ) (hr : 1<R) :
    (Real.cosh (tortoise R):ℂ)^(2 : ℕ)=((R:ℂ)^(2 : ℕ))/((R:ℂ)^(2 : ℕ)-1) := by
  have hm : R-1≠0 := by linarith
  have hp : R+1≠0 := by linarith
  have hf : R^(2 : ℕ)-1≠0 := by nlinarith
  have he : Real.exp (2*tortoise R)=(R-1)/(R+1) := by
    rw [tortoise,mul_div_cancel₀ _ (by norm_num : (2:ℝ)≠0),Real.exp_sub,
      Real.exp_log (by linarith : 0<R-1),Real.exp_log (by linarith : 0<R+1)]
  have hc (t : ℝ) : (Real.cosh t)^(2 : ℕ)=(Real.exp (2*t)+2+(Real.exp (2*t))⁻¹)/4 := by
    have hn := (Real.exp_pos t).ne'
    have ht : Real.exp (2*t)=(Real.exp t)^(2 : ℕ) := by rw [two_mul,Real.exp_add,pow_two]
    rw [ht,Real.cosh_eq,Real.exp_neg]
    field_simp
    ring
  have hh : (Real.cosh (tortoise R))^(2 : ℕ)=R^(2 : ℕ)/(R^(2 : ℕ)-1) := by
    rw [hc,he]
    field_simp
    ring
  exact_mod_cast hh

private theorem chart_radial_wave {f : F} {x : P} (hr : 1<x 1) (hy : 0<x 3)
    (hf : ContDiffAt ℝ 2 f (chart x)) :
    ((x 1:ℂ)^(2 : ℕ)-1)*coordDeriv 1 (coordDeriv 1 (fun z => f (chart z))) x+
      2*coordDeriv 0 (coordDeriv 1 (fun z => f (chart z))) x+
      2*(x 1:ℂ)*coordDeriv 1 (fun z => f (chart z)) x=
      -4/((x 1:ℂ)^(2 : ℕ)-1)*coordDeriv 0 (coordDeriv 1 f) (chart x) := by
  rw [chart_radial_second hr hy hf 1,chart_radial_second hr hy hf 0,
    chart_first hr hy (hf.differentiableAt (by norm_num)) 1]
  simp only [pullFirst,radialMultiplier,Matrix.cons_val_zero,Matrix.cons_val_one,
    ite_true,zero_ne_one,ite_false,zero_mul,zero_add]
  have hne : (x 1:ℂ)^(2 : ℕ)-1≠0 := by exact_mod_cast (show x 1^(2 : ℕ)-1≠0 by nlinarith)
  field_simp
  ring

private theorem chart_angular_wave {f : F} {x : P} (hr : 1<x 1) (hy : 0<x 3)
    (hf : ContDiffAt ℝ 2 f (chart x)) :
    angularLap (fun z => f (chart z)) x=nativeLap f (chart x) := by
  unfold angularLap nativeLap
  rw [chart_horizontal_second hr hy hf,chart_height_second hr hy hf]
  have he : Real.exp (chart x 3)=x 3 := by simp [chart,Real.exp_log hy]
  rw [he]
  have hn : (x 3:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hy.ne'
  field_simp
  ring

/-- Complete original forcing in the original physical ingoing chart. -/
def originalForcing (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (x : P) : ℂ :=
  D4BMJointSource.timeOriginalForcing q branch amp
    (x 0-tortoise (x 1)) (tortoise (x 1)) ![x 2,x 3]

/-- The actual original causal field satisfies the ingoing wave equation, including the lift. -/
theorem original_ingoing_wave (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (x : P) (hp : 0<x 0) (hr : 1<x 1) (hy : 0<x 3) :
    let V := D4BMActualIngoingCurrent.originalIngoingPotential q branch amp
    ((x 1:ℂ)^(2 : ℕ)-1)*coordDeriv 1 (coordDeriv 1 V) x+
      2*coordDeriv 0 (coordDeriv 1 V) x+2*(x 1:ℂ)*coordDeriv 1 V x+
      angularLap V x/(x 1:ℂ)^(2 : ℕ)= -originalForcing q branch amp x/((x 1:ℂ)^(2 : ℕ)-1) := by
  let f := nativeField q branch amp
  have hpr : chart x 0<chart x 1 := by
    change x 0<x 0-2*tortoise (x 1)
    linarith [tortoise_neg (x 1) hr]
  have hs := D4BMOriginalSpacetimeRegularity.originalPotential_smooth q branch amp
    (chart x) hp hpr
  have hs2 : ContDiffAt ℝ 2 f (chart x) := hs.of_le (WithTop.coe_le_coe.mpr le_top)
  have hw := native_wave q branch amp (chart x) hp hpr
  have htime : (chart x 0+chart x 1)/2=x 0-tortoise (x 1) := by dsimp [chart];ring
  have hrad : (chart x 0-chart x 1)/2=tortoise (x 1) := by dsimp [chart];ring
  have hpoint : ![chart x 2,Real.exp (chart x 3)]=![x 2,x 3] := by simp [chart,Real.exp_log hy]
  rw [htime,hrad,hpoint] at hw
  change 4*coordDeriv 0 (coordDeriv 1 f) (chart x)-nativeLap f (chart x)/
    (Real.cosh (tortoise (x 1)):ℂ)^(2 : ℕ)=originalForcing q branch amp x at hw
  change ((x 1:ℂ)^(2 : ℕ)-1)*coordDeriv 1 (coordDeriv 1 (fun z => f (chart z))) x+
      2*coordDeriv 0 (coordDeriv 1 (fun z => f (chart z))) x+
      2*(x 1:ℂ)*coordDeriv 1 (fun z => f (chart z)) x+
      angularLap (fun z => f (chart z)) x/(x 1:ℂ)^(2 : ℕ)=_
  rw [chart_radial_wave hr hy hs2,chart_angular_wave hr hy hs2,← hw,
    tortoise_cosh_weight (x 1) hr]
  have hR : (x 1:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (by linarith)
  have hF : (x 1:ℂ)^(2 : ℕ)-1≠0 := by exact_mod_cast (show x 1^(2 : ℕ)-1≠0 by nlinarith)
  field_simp
  ring

private def contactJet (r : ℂ) (J : ScalarTwoJet (Fin 4) ℂ) : ℂ :=
  -r^(2 : ℕ)*(r^(2 : ℕ)-1)*J.second 1 1-r^(2 : ℕ)*(J.second 0 1+J.second 1 0)-
    2*r*J.first 1+2*r*J.first 0

/-- The scalar contact whose coexact field is the actual reconstructed Einstein contact. -/
def scalarContact (u : F) (x : P) : ℂ := contactJet (x 1) (ofField u x)

private theorem radius_contact {v : F} {x : P} (hv : ContDiffAt ℝ 2 v x) :
    scalarContact (fun z => (z 1:ℂ)*v z) x=
      -(x 1:ℂ)^(3 : ℕ)*(((x 1:ℂ)^(2 : ℕ)-1)*coordDeriv 1 (coordDeriv 1 v) x+
        coordDeriv 0 (coordDeriv 1 v) x+coordDeriv 1 (coordDeriv 0 v) x+
        2*(x 1:ℂ)*coordDeriv 1 v x)-2*(x 1:ℂ)*v x := by
  have hc : ContDiffAt ℝ 2 (fun z : P => (z 1:ℂ)) x :=
    (Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ 1)).contDiffAt
  unfold scalarContact
  rw [ofField_mul hc hv,D4BMFundamentalScalarMetric.coordinate_jet]
  simp only [contactJet,ScalarTwoJet.mul,D4BMFundamentalScalarMetric.coordinateJet,ofField,
    ite_true,zero_ne_one,ite_false,zero_mul,add_zero,zero_add]
  ring

private theorem radius_angularLap {v : F} {x : P} (hv : ContDiffAt ℝ 2 v x) :
    angularLap (fun z => (z 1:ℂ)*v z) x=(x 1:ℂ)*angularLap v x := by
  have hc : ContDiffAt ℝ 2 (fun z : P => (z 1:ℂ)) x :=
    (Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ 1)).contDiffAt
  have hj := ofField_mul hc hv
  rw [D4BMFundamentalScalarMetric.coordinate_jet] at hj
  have h2 := congrArg (fun J => J.second 2 2) hj
  have h3 := congrArg (fun J => J.second 3 3) hj
  unfold angularLap
  change (x 3:ℂ)^(2 : ℕ)*((ofField (fun z => (z 1:ℂ)*v z) x).second 2 2+
    (ofField (fun z => (z 1:ℂ)*v z) x).second 3 3)=_
  rw [h2,h3]
  simp only [ScalarTwoJet.mul,D4BMFundamentalScalarMetric.coordinateJet,ofField]
  simp only [show (2:Fin 4)≠1 by decide,show (3:Fin 4)≠1 by decide,ite_false,zero_mul,zero_add,add_zero]
  ring

/-- Source contact of the original radius-weighted causal field, with its full forcing. -/
theorem original_scalar_contact (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (x : P) (hp : 0<x 0) (hr : 1<x 1) (hy : 0<x 3) :
    scalarContact (sourceScalar q branch amp) x=
      angularLap (sourceScalar q branch amp) x-2*sourceScalar q branch amp x+
        (x 1:ℂ)^(3 : ℕ)/((x 1:ℂ)^(2 : ℕ)-1)*originalForcing q branch amp x := by
  let V := D4BMActualIngoingCurrent.originalIngoingPotential q branch amp
  have hs : ContDiffAt ℝ 2 V x :=
    (D4BMOriginalGreenBoundary.originalPotential_exterior_smooth q branch amp x hp hr hy).of_le (WithTop.coe_le_coe.mpr le_top)
  have hw := original_ingoing_wave q branch amp x hp hr hy
  change ((x 1:ℂ)^(2 : ℕ)-1)*coordDeriv 1 (coordDeriv 1 V) x+
    2*coordDeriv 0 (coordDeriv 1 V) x+2*(x 1:ℂ)*coordDeriv 1 V x+
    angularLap V x/(x 1:ℂ)^(2 : ℕ)= -originalForcing q branch amp x/((x 1:ℂ)^(2 : ℕ)-1) at hw
  change scalarContact (fun z => (z 1:ℂ)*V z) x=
    angularLap (fun z => (z 1:ℂ)*V z) x-2*((x 1:ℂ)*V x)+_
  rw [radius_contact hs,radius_angularLap hs,coordDeriv_comm hs 1 0]
  have hR : (x 1:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (by linarith)
  have hF : (x 1:ℂ)^(2 : ℕ)-1≠0 := by exact_mod_cast (show x 1^(2 : ℕ)-1≠0 by nlinarith)
  linear_combination (norm := (field_simp [hR,hF]; ring)) -(x 1:ℂ)^(3 : ℕ)*hw

private theorem smooth_partial {u : F} {x : P} (hu : ContDiffAt ℝ ∞ u x) (i : Fin 4) :
    ContDiffAt ℝ ∞ (coordDeriv i u) x := coordDeriv_contDiffAt hu (by simp) i

private theorem smooth_two {u : F} {x : P} (hu : ContDiffAt ℝ ∞ u x) :
    ContDiffAt ℝ 2 u x := hu.of_le (WithTop.coe_le_coe.mpr le_top)

private theorem partial_triple {u : F} {x : P} (hu : ContDiffAt ℝ ∞ u x) (i j k : Fin 4) :
    coordDeriv i (coordDeriv j (coordDeriv k u)) x=
      coordDeriv j (coordDeriv k (coordDeriv i u)) x := by
  rw [coordDeriv_comm (smooth_two (smooth_partial hu k)) i j]
  have he : coordDeriv i (coordDeriv k u) =ᶠ[𝓝 x] coordDeriv k (coordDeriv i u) := by
    filter_upwards [(smooth_two hu).eventually (by norm_num)] with z hz
    exact coordDeriv_comm hz i k
  exact congrArg (fun L => L (Pi.single j 1)) (he.fderiv_eq (𝕜 := ℝ))

private theorem scalarContact_angular_partial {u : F} {x : P}
    (hu : ContDiffAt ℝ ∞ u x) (i : Fin 4) (hi : i≠1) :
    coordDeriv i (scalarContact u) x=scalarContact (coordDeriv i u) x := by
  have hR := Complex.ofRealCLM.hasFDerivAt.comp x (hasFDerivAt_apply 1 x)
  have hd (j : Fin 4) := ((smooth_partial hu j).differentiableAt (by simp)).hasFDerivAt
  have hdd (j k : Fin 4) :=
    ((smooth_partial (smooth_partial hu k) j).differentiableAt (by simp)).hasFDerivAt
  have hA := (((hR.pow 2).neg.mul ((hR.pow 2).sub_const 1)).mul (hdd 1 1))
  have hB := (hR.pow 2).mul ((hdd 0 1).add (hdd 1 0))
  have h := ((hA.sub hB).sub ((hR.const_mul 2).mul (hd 1))).add
    ((hR.const_mul 2).mul (hd 0))
  change coordDeriv i (fun z => -(z 1:ℂ)^(2 : ℕ)*((z 1:ℂ)^(2 : ℕ)-1)*coordDeriv 1 (coordDeriv 1 u) z-
    (z 1:ℂ)^(2 : ℕ)*(coordDeriv 0 (coordDeriv 1 u) z+coordDeriv 1 (coordDeriv 0 u) z)-
    2*(z 1:ℂ)*coordDeriv 1 u z+2*(z 1:ℂ)*coordDeriv 0 u z) x=_
  simp only [Function.comp_def,Complex.ofRealCLM_apply,Pi.mul_apply,Pi.add_apply,
    Pi.neg_apply] at h
  change HasFDerivAt (scalarContact u) _ x at h
  change fderiv ℝ (scalarContact u) x (Pi.single i 1)=_
  rw [h.fderiv]
  simp only [add_apply,sub_apply,neg_apply,smul_apply,smul_eq_mul,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.proj_apply,Complex.ofRealCLM_apply,
    Pi.single_eq_of_ne (Ne.symm hi),Complex.ofReal_zero,mul_zero,add_zero,neg_zero]
  change -(x 1:ℂ)^(2 : ℕ)*((x 1:ℂ)^(2 : ℕ)-1)*coordDeriv i (coordDeriv 1 (coordDeriv 1 u)) x-
    (x 1:ℂ)^(2 : ℕ)*(coordDeriv i (coordDeriv 0 (coordDeriv 1 u)) x+
      coordDeriv i (coordDeriv 1 (coordDeriv 0 u)) x)-
    2*(x 1:ℂ)*coordDeriv i (coordDeriv 1 u) x+
    2*(x 1:ℂ)*coordDeriv i (coordDeriv 0 u) x=_
  rw [partial_triple hu i 1 1,partial_triple hu i 0 1,partial_triple hu i 1 0,
    coordDeriv_comm (smooth_two hu) i 1,coordDeriv_comm (smooth_two hu) i 0]
  rfl

/-- The full reconstructed contact is the coexact scalar contact, with genuine third derivatives. -/
theorem coexact_contact {u : F} {x : P} (hu : ContDiffAt ℝ ∞ u x) (a : Fin 2) :
    D4BMIngoingFullCurrent.contact (x 1) (x 3) (fun j => ofField (coexactField u j) x) a=
      coexactField (scalarContact u) a x := by
  have hbase :
      D4BMIngoingFullCurrent.contact (x 1) (x 3) (fun j => ofField (coexactField u j) x) a=
        scalarContact (coexactField u a) x := by
    unfold D4BMIngoingFullCurrent.contact D4BMIngoingFullCurrent.master scalarContact contactJet
    ring
  rw [hbase]
  fin_cases a
  · change scalarContact (coordDeriv 3 u) x=coordDeriv 3 (scalarContact u) x
    exact (scalarContact_angular_partial hu 3 (by decide)).symm
  · have hn (v : F) : scalarContact (fun z => -v z) x= -scalarContact v x := by
      unfold scalarContact
      rw [ofField_neg]
      simp only [contactJet,ScalarTwoJet.neg]
      ring
    change scalarContact (fun z => -coordDeriv 2 u z) x= -coordDeriv 2 (scalarContact u) x
    rw [hn,scalarContact_angular_partial hu 2 (by decide)]

/-- The actual original stream contact retains the full causal forcing and angular source. -/
theorem original_stream_contact (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (x : P) (hp : 0<x 0) (hr : 1<x 1) (hy : 0<x 3) (a : Fin 2) :
    D4BMIngoingFullCurrent.contact (x 1) (x 3)
      (fun j => ofField (D4BMActualIngoingCurrent.originalStream q branch amp j) x) a=
      coexactField (fun z => angularLap (sourceScalar q branch amp) z-
        2*sourceScalar q branch amp z+
        (z 1:ℂ)^(3 : ℕ)/((z 1:ℂ)^(2 : ℕ)-1)*originalForcing q branch amp z) a x := by
  have hu := D4BMOriginalGreenBoundary.sourceScalar_exterior_smooth q branch amp x hp hr hy
  have hs := D4BMOriginalGreenBoundary.originalPotential_exterior_smooth q branch amp x hp hr hy
  have hj (j : Fin 2) : ofField (coexactField (sourceScalar q branch amp) j) x=
      ofField (D4BMActualIngoingCurrent.originalStream q branch amp j) x := by
    apply ofField_germ
    filter_upwards [(smooth_two hs).eventually (by norm_num)] with z hz
    exact source_coexact q branch amp z (hz.differentiableAt (by norm_num)) j
  simp_rw [← hj]
  rw [coexact_contact hu]
  have he : scalarContact (sourceScalar q branch amp) =ᶠ[𝓝 x]
      (fun z => angularLap (sourceScalar q branch amp) z-2*sourceScalar q branch amp z+
        (z 1:ℂ)^(3 : ℕ)/((z 1:ℂ)^(2 : ℕ)-1)*originalForcing q branch amp z) := by
    filter_upwards [(isOpen_lt continuous_const (continuous_apply 0)).mem_nhds hp,
      (isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hr,
      (isOpen_lt continuous_const (continuous_apply 3)).mem_nhds hy] with z hzp hzr hzy
    exact original_scalar_contact q branch amp z hzp hzr hzy
  have hd (i : Fin 4) := congrArg (fun L => L (Pi.single i 1)) (he.fderiv_eq (𝕜 := ℝ))
  fin_cases a
  · exact hd 3
  · exact congrArg Neg.neg (hd 2)


end RHTower.D4BMOriginalSourceContact
