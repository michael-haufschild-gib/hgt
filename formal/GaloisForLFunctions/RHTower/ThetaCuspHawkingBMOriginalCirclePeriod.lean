import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalScalarPairing
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalCausalRestoration
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativeModularTransport

/-!
# Original circle period in the temporal/metric comparison

The complete native circle mean has an actual three-power finite part, with its
original zero-radius value. All mixed residual jets have uniform height bounds
on compact radius intervals. These bounds admit parameter differentiation of
the physical scalar integral and its first two radius derivatives.

The scalar Green identity retains the complete curved modular domain and its
top flux. The physical Legendre reader kernel never vanishes. The limiting
Green equation and full temporal/metric/QNM matching remain to be established.
-/

open Set Filter Topology MeasureTheory UpperHalfPlane ModularGroup
open scoped ContDiff MatrixGroups
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal
attribute [-instance] RCLike.innerProductSpace
namespace RHTower.D4BMOriginalCircleGreen
open GaloisForLFunctions.HTGeometry ScalarTwoJet D4BMHorizon D4BMModularCore
open D4BMJointSource D4BMGlobalAngularResponse

def circleField (q : XiZeroCopy) (d : ℝ) (z : Point) : ℂ :=
  D4BMNativeCircle.mean q d (z 0) (Real.log (z 1))

private theorem source_smooth (q : XiZeroCopy) (d : ℝ)
    (z : Point) (hz : 0 < z 1) : ContDiffAt ℝ ∞ (circleField q d) z := by
  have hc : ContDiffAt ℝ ∞ (fun w : Point => (d,w 0,Real.log (w 1))) z :=
    contDiffAt_const.prodMk ((contDiff_apply ℝ ℝ (0:Fin 2)).contDiffAt.prodMk
      ((contDiff_apply ℝ ℝ (1:Fin 2)).contDiffAt.log hz.ne'))
  have hm : ContDiff ℝ ∞ (fun v : ℝ × ℝ × ℝ => D4BMNativeCircle.mean q v.1 v.2.1 v.2.2) :=
    D4BMNativeResponse.nativeMean_joint_smooth q
  have h := hm.contDiffAt.comp z hc
  change ContDiffAt ℝ ∞ ((fun v : ℝ × ℝ × ℝ =>
    D4BMNativeCircle.mean q v.1 v.2.1 v.2.2) ∘
      (fun w : Point => (d,w 0,Real.log (w 1)))) z at h
  exact h

private theorem reader_smooth (q : XiZeroCopy) (z : Point) (hz : 0 < z 1) :
    ContDiffAt ℝ ∞ (D4BMLiteralCusp.scalar (physicalAngularParameter q)) z :=
  (D4BMAngularSeries.cuspLeg_contDiffOn .scalar (physicalAngularParameter q)).contDiffAt
    ((isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hz)

private theorem source_modular (q : XiZeroCopy) (d : ℝ)
    (A : SL(2,ℤ)) (z : UpperHalfPlane) :
    circleField q d (coordinates (A • z))=circleField q d (coordinates z) :=
  D4BMNativeCircle.mean_modular q d A z

private def differential (F : Point → ℂ) (z : UpperHalfPlane) (v : ℂ) : ℂ :=
  fderiv ℝ ((fun w : UpperHalfPlane => F (coordinates w)) ∘ ofComplex) (z:ℂ) v

private theorem differential_components (F : Point → ℂ) (z : UpperHalfPlane) (v : ℂ) :
    differential F z v = (v.re:ℂ)*coordDeriv 0 F (coordinates z)+
      (v.im:ℂ)*coordDeriv 1 F (coordinates z) := by
  have he : (fun w : UpperHalfPlane => F (coordinates w)) ∘ ofComplex =ᶠ[𝓝 (z:ℂ)]
      F ∘ angularCoordinates := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
    simp only [Function.comp_apply,coordinates,ofComplex_apply_of_im_pos hw,angularCoordinates]
    rfl
  have hv : v = v.re • (1:ℂ)+v.im • Complex.I := by
    simpa only [Complex.real_smul,mul_one] using v.re_add_im.symm
  have hx := angularCoordinates_derivative F 0 (z:ℂ)
  have hy := angularCoordinates_derivative F 1 (z:ℂ)
  simp only [direction,Matrix.cons_val_zero,Matrix.cons_val_one] at hx hy
  unfold differential
  rw [he.fderiv_eq,hv,map_add,map_smul,map_smul,hx,hy]
  simp [Complex.real_smul,angularCoordinates,coordinates]

private theorem differential_modular (F : Point → ℂ)
    (hF : ∀ z, 0 < z 1 → ContDiffAt ℝ ∞ F z) (A : SL(2,ℤ))
    (hi : ∀ z, F (coordinates (A • z))=F (coordinates z)) (z : UpperHalfPlane) (v : ℂ) :
    differential F z v=differential F (A • z) ((1/(denom A z)^(2 : ℕ))*v) := by
  have he : (fun w : UpperHalfPlane => F (coordinates (A • w))) =
      (fun w => F (coordinates w)) := funext hi
  have h := chart_fderiv_modular_pullback A (fun w => F (coordinates w))
    (chartSmooth_coordinates F hF) z
  rw [he] at h
  unfold differential
  rw [h,ContinuousLinearMap.comp_apply,modular_chart_jacobian]

/-- Scalar Green flux for the actual circle mean and the unchanged physical reader. -/
def flux (F : Point → ℂ) (u : ℂ) (j : Fin 2) (z : Point) : ℂ :=
  D4BMLiteralCusp.scalar u z*coordDeriv j F z-F z*coordDeriv j (D4BMLiteralCusp.scalar u) z

def defect (F : Point → ℂ) (u : ℂ) (z : Point) : ℂ :=
  (D4BMLiteralCusp.scalar u z*scalarLaplacian F z-
    (u^(2 : ℕ)-1/4)*D4BMLiteralCusp.scalar u z*F z)/(z 1:ℂ)^(2 : ℕ)

private theorem partial_smooth {F : Point → ℂ} {z : Point} (hF : ContDiffAt ℝ ∞ F z) (j : Fin 2) :
    ContDiffAt ℝ ∞ (coordDeriv j F) z := coordDeriv_contDiffAt hF (by simp) j

private theorem divergence_flux {F : Point → ℂ} {z : Point} (hF : ContDiffAt ℝ ∞ F z)
    (hz : 0<z 1) (u : ℂ) :
    (∑ j : Fin 2, coordDeriv j (flux F u j) z)=defect F u z := by
  have hS : ContDiffAt ℝ ∞ (D4BMLiteralCusp.scalar u) z :=
    (D4BMAngularSeries.cuspLeg_contDiffOn .scalar u).contDiffAt
      ((isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hz)
  have hd (j : Fin 2) : coordDeriv j (flux F u j) z=
      (coordDeriv j (D4BMLiteralCusp.scalar u) z*coordDeriv j F z+
        D4BMLiteralCusp.scalar u z*coordDeriv j (coordDeriv j F) z)-
      (coordDeriv j F z*coordDeriv j (D4BMLiteralCusp.scalar u) z+
        F z*coordDeriv j (coordDeriv j (D4BMLiteralCusp.scalar u)) z) := by
    unfold flux
    rw [coordDeriv_sub ((hS.mul (partial_smooth hF j)).differentiableAt (by simp))
      ((hF.mul (partial_smooth hS j)).differentiableAt (by simp))]
    rw [coordDeriv_mul (hS.differentiableAt (by simp))
      ((partial_smooth hF j).differentiableAt (by simp)),
      coordDeriv_mul (hF.differentiableAt (by simp))
      ((partial_smooth hS j).differentiableAt (by simp))]
  have he := D4BMLiteralCusp.scalar_equation u z hz
  rw [scalarLaplacian_eq _ z hz] at he
  simp only [D4BMLiteralCusp.scalarQ,neg_sub] at he
  have hn : (z 1:ℂ)^(2 : ℕ) ≠ 0 := pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr hz.ne')
  simp only [Fin.sum_univ_two,hd,defect,scalarLaplacian_eq _ z hz]
  apply (eq_div_iff hn).mpr
  linear_combination -F z*he

/-- The complete original top normal flux at a finite modular cusp cutoff. -/
def normalFlux (q r : XiZeroCopy) (d Y : ℝ) : ℂ :=
  ∫ X in (-(1/2:ℝ))..1/2,
    flux (circleField q d) (physicalAngularParameter r) 1 ![X,Y]

/-- Contraction of the original transfer flux with an arbitrary real tangent direction. -/
def current (q r : XiZeroCopy) (d : ℝ)
    (z : UpperHalfPlane) (a : ℂ) : ℂ :=
  (a.re:ℂ)*flux (circleField q d) (physicalAngularParameter r) 0 (coordinates z)+
    (a.im:ℂ)*flux (circleField q d) (physicalAngularParameter r) 1 (coordinates z)

private theorem current_differential (q r : XiZeroCopy) (d : ℝ)
    (z : UpperHalfPlane) (a : ℂ) :
    current q r d z a =
      D4BMLiteralCusp.scalar (physicalAngularParameter r) (coordinates z)*
        differential (circleField q d) z a-
      circleField q d (coordinates z)*
        differential (D4BMLiteralCusp.scalar (physicalAngularParameter r)) z a := by
  rw [differential_components,differential_components]
  unfold current flux
  ring

/-- The source value and reader differential give their original modular normal current. -/
theorem current_modular (q r : XiZeroCopy) (d : ℝ)
    (A : SL(2,ℤ)) (z : UpperHalfPlane) (a : ℂ) :
    current q r d z a =
      current q r d (A • z) ((1/(denom A z)^(2 : ℕ))*a) := by
  rw [current_differential,current_differential,source_modular,
    show D4BMLiteralCusp.scalar (physicalAngularParameter r) (coordinates (A • z))=
      D4BMLiteralCusp.scalar (physicalAngularParameter r) (coordinates z) from physicalScalar_modular r A z,
    differential_modular _ (source_smooth q d) A (source_modular q d A),
    differential_modular _ (reader_smooth r) A (physicalScalar_modular r A)]

/-- The actual radial current reverses sign under inversion, including all causal and Fourier tails. -/
theorem current_radial_inversion (q r : XiZeroCopy) (d : ℝ)
    (z : UpperHalfPlane) :
    current q r d z (z:ℂ)+
      current q r d (S • z) ((S • z:UpperHalfPlane):ℂ)=0 := by
  have h := current_modular q r d S z (z:ℂ)
  have hv : (1/(denom S z)^(2 : ℕ))*(z:ℂ) = -((S • z:UpperHalfPlane):ℂ) := by
    simp only [UpperHalfPlane.modular_S_smul]
    simp [denom,ModularGroup.S,inv_neg]
    field_simp
  rw [hv] at h
  have hn : current q r d (S • z) (-((S • z:UpperHalfPlane):ℂ)) =
      -current q r d (S • z) ((S • z:UpperHalfPlane):ℂ) := by
    simp only [current,Complex.neg_re,Complex.neg_im,Complex.ofReal_neg]
    ring
  rw [hn] at h
  rw [h]
  ring

private theorem coordinates_point (x : ℝ) {y : ℝ} (hy : 0 < y) :
    coordinates (ofComplex (GaloisForLFunctions.RHTower.SelbergMaassMean.point x y))=![x,y] := by
  ext i
  fin_cases i <;> simp [coordinates,ofComplex_apply_of_im_pos,
    GaloisForLFunctions.RHTower.SelbergMaassMean.point,hy]

/-- The original current's paired vertical sides agree. -/
theorem original_side_cancellation (q r : XiZeroCopy) (d : ℝ)
    {y : ℝ} (hy : 0 < y) :
    flux (circleField q d) (physicalAngularParameter r) 0 ![1/2,y]=
      flux (circleField q d) (physicalAngularParameter r) 0 ![-(1/2),y] := by
  have h := current_modular q r d T
    (ofComplex (GaloisForLFunctions.RHTower.SelbergMaassMean.point (-(1/2)) y)) 1
  rw [GaloisForLFunctions.RHTower.SelbergMaassTraceBoundary.translation_point _ hy,
    show -(1/2:ℝ)+1=1/2 by ring] at h
  simpa [current,denom,ModularGroup.T,coordinates_point _ hy] using h.symm

/-- Literal oriented unit-circle fluxes cancel for the complete original source and reader. -/
theorem original_arc_cancellation (q r : XiZeroCopy) (d : ℝ)
    {x y : ℝ} (hy : 0 < y) (hxy : x^(2 : ℕ)+y^(2 : ℕ)=1) :
    ((x/y:ℝ):ℂ)*(flux (circleField q d) (physicalAngularParameter r) 0 ![-x,y]-
      flux (circleField q d) (physicalAngularParameter r) 0 ![x,y])-
      flux (circleField q d) (physicalAngularParameter r) 1 ![-x,y]-
      flux (circleField q d) (physicalAngularParameter r) 1 ![x,y]=0 := by
  let z := ofComplex (GaloisForLFunctions.RHTower.SelbergMaassMean.point x y)
  have h := current_radial_inversion q r d z
  dsimp only [z] at h
  rw [GaloisForLFunctions.RHTower.SelbergMaassTraceBoundary.inversion_on_unit_circle hy hxy] at h
  have hp (t : ℝ) : 0 < (GaloisForLFunctions.RHTower.SelbergMaassMean.point t y).im := by
    simpa [GaloisForLFunctions.RHTower.SelbergMaassMean.point] using hy
  unfold current at h
  rw [coordinates_point x hy,coordinates_point (-x) hy,
    ofComplex_apply_of_im_pos (hp x),ofComplex_apply_of_im_pos (hp (-x))] at h
  simp only [GaloisForLFunctions.RHTower.SelbergMaassMean.point,
    Complex.add_re,Complex.add_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.mul_I_re,Complex.mul_I_im,neg_zero,add_zero,zero_add,Complex.ofReal_neg,
    Complex.neg_re,Complex.neg_im] at h
  rw [Complex.ofReal_div]
  field_simp [Complex.ofReal_ne_zero.mpr hy.ne']
  linear_combination -h


private theorem flux_smooth (q r : XiZeroCopy) (d : ℝ)
    (j : Fin 2) (z : Point) (hz : 0 < z 1) :
    ContDiffAt ℝ ∞ (flux (circleField q d) (physicalAngularParameter r) j) z := by
  have hZ := source_smooth q d z hz
  have hS := reader_smooth r z hz
  exact (hS.mul (partial_smooth hZ j)).sub (hZ.mul (partial_smooth hS j))

private def planarFlux (q r : XiZeroCopy) (d : ℝ)
    (j : Fin 2) : ℂ → ℂ :=
  flux (circleField q d) (physicalAngularParameter r) j ∘ angularCoordinates

private theorem planarFlux_smooth (q r : XiZeroCopy) (d : ℝ)
    (j : Fin 2) : ContDiffOn ℝ ∞ (planarFlux q r d j) {z : ℂ | 0 < z.im} := by
  intro z hz
  exact ((flux_smooth q r d j (angularCoordinates z) hz).comp z
    angularCoordinates.contDiff.contDiffAt).contDiffWithinAt

private theorem planarFlux_point (q r : XiZeroCopy) (d : ℝ)
    (j : Fin 2) (x y : ℝ) :
    planarFlux q r d j (GaloisForLFunctions.RHTower.SelbergMaassMean.point x y)=
      flux (circleField q d) (physicalAngularParameter r) j ![x,y] := by
  have hp : angularCoordinates (GaloisForLFunctions.RHTower.SelbergMaassMean.point x y)=![x,y] := by
    ext i
    fin_cases i <;> simp [angularCoordinates,GaloisForLFunctions.RHTower.SelbergMaassMean.point]
  exact congrArg (flux (circleField q d) (physicalAngularParameter r) j) hp

private theorem projected_derivative (q r : XiZeroCopy) (d : ℝ)
    (j i : Fin 2) (L : ℂ →L[ℝ] ℝ) (z : ℂ) (hz : 0 < z.im) :
    fderiv ℝ (L ∘ planarFlux q r d j) z (direction i)=
      L (coordDeriv i (flux (circleField q d)
        (physicalAngularParameter r) j) (angularCoordinates z)) := by
  have hf := ((planarFlux_smooth q r d j).contDiffAt
    (isOpen_upperHalfPlaneSet.mem_nhds hz)).differentiableAt (by simp)
  rw [(L.hasFDerivAt.comp z hf.hasFDerivAt).fderiv,ContinuousLinearMap.comp_apply]
  exact congrArg L (angularCoordinates_derivative _ i z)

private theorem projected_divergence (q r : XiZeroCopy) (d : ℝ)
    (L : ℂ →L[ℝ] ℝ) (z : ℂ) (hz : 0 < z.im) :
    fderiv ℝ (L ∘ planarFlux q r d 0) z 1+
      fderiv ℝ (L ∘ planarFlux q r d 1) z Complex.I=
    L (defect (circleField q d) (physicalAngularParameter r) (angularCoordinates z)) := by
  have h0 := projected_derivative q r d 0 0 L z hz
  have h1 := projected_derivative q r d 1 1 L z hz
  simp only [direction,Matrix.cons_val_zero,Matrix.cons_val_one] at h0 h1
  rw [h0,h1,← map_add]
  congr 1
  simpa only [Fin.sum_univ_two] using
    divergence_flux (source_smooth q d (angularCoordinates z) hz) hz (physicalAngularParameter r)

open GaloisForLFunctions.RHTower

private theorem defect_continuous (q r : XiZeroCopy) (d : ℝ) :
    ContinuousOn (defect (circleField q d) (physicalAngularParameter r))
      {z : Point | 0 < z 1} := by
  have hd : ContinuousOn (fun z : Point =>
      coordDeriv 0 (flux (circleField q d) (physicalAngularParameter r) 0) z+
      coordDeriv 1 (flux (circleField q d) (physicalAngularParameter r) 1) z)
      {z : Point | 0 < z 1} := by
    intro z hz
    exact ((partial_smooth (flux_smooth q r d 0 z hz) 0).continuousAt.add
      (partial_smooth (flux_smooth q r d 1 z hz) 1).continuousAt).continuousWithinAt
  apply hd.congr
  intro z hz
  simpa only [Fin.sum_univ_two] using
    (divergence_flux (source_smooth q d z hz) hz (physicalAngularParameter r)).symm

private theorem defect_integrable (q r : XiZeroCopy) (d Y : ℝ) :
    IntegrableOn (fun w : ℝ × ℝ => defect (circleField q d)
      (physicalAngularParameter r) ![w.1,w.2]) (SelbergModularDomainSlices.domain Y) := by
  have hc : ContinuousOn (fun w : ℝ × ℝ => defect (circleField q d)
      (physicalAngularParameter r) ![w.1,w.2]) (SelbergModularDomainSlices.cell Y) := by
    apply (defect_continuous q r d).comp
      (show Continuous (fun w : ℝ × ℝ => (![w.1,w.2] : Point)) by
        apply continuous_pi; intro i; fin_cases i <;> fun_prop).continuousOn
    intro w hw
    change 0 < w.2
    linarith [hw.2.1]
  exact (hc.mono (SelbergModularDomainSlices.domain_subset_cell Y)).integrableOn_compact
    (SelbergModularDomainSlices.isCompact_domain Y)

private theorem flux_integrable (q r : XiZeroCopy) (d Y : ℝ)
    (hY : 0 < Y) : IntervalIntegrable (fun x : ℝ =>
      flux (circleField q d) (physicalAngularParameter r) 1 ![x,Y])
      volume (-(1/2:ℝ)) (1/2) := by
  have hmap : Continuous (fun x : ℝ => (![x,Y] : Point)) := by
    apply continuous_pi; intro i; fin_cases i <;> fun_prop
  apply Continuous.intervalIntegrable
  apply continuous_iff_continuousAt.mpr
  intro x
  exact (flux_smooth q r d 1 ![x,Y] hY).continuousAt.comp
    (f := fun t : ℝ => (![t,Y] : Point)) (x := x) hmap.continuousAt

private theorem projected_area (q r : XiZeroCopy) (d : ℝ)
    (L : ℂ →L[ℝ] ℝ) {Y : ℝ} (hY : 1 ≤ Y) :
    (∫ w in SelbergModularDomainSlices.domain Y,
      L (defect (circleField q d) (physicalAngularParameter r) ![w.1,w.2]))=
      ∫ x in (-(1/2:ℝ))..1/2,
        L (flux (circleField q d) (physicalAngularParameter r) 1 ![x,Y]) := by
  let F := planarFlux q r d
  have hF (j : Fin 2) : ContDiffOn ℝ 1 (L ∘ F j) {z : ℂ | 0 < z.im} :=
    L.contDiff.comp_contDiffOn ((contDiffOn_infty.mp (planarFlux_smooth q r d j)) 1)
  have h := SelbergModularCurrentGreen.current_green_identity (L ∘ F 0) (hF 0)
    (L ∘ F 1) (hF 1) hY
  have hd : (∫ w in SelbergModularDomainSlices.domain Y,
      SelbergMaassTraceEnergy.dir 1 (L ∘ F 0) (SelbergMaassMean.point w.1 w.2)+
      SelbergMaassTraceEnergy.dir Complex.I (L ∘ F 1) (SelbergMaassMean.point w.1 w.2))=
      ∫ w in SelbergModularDomainSlices.domain Y,
        L (defect (circleField q d) (physicalAngularParameter r) ![w.1,w.2]) := by
    apply setIntegral_congr_fun (SelbergModularDomainSlices.isCompact_domain Y).measurableSet
    intro w hw
    have hw0 : 0 < w.2 := by linarith [hw.1.2.1]
    have hh := projected_divergence q r d L (SelbergMaassMean.point w.1 w.2)
      (by simpa [SelbergMaassMean.point] using hw0)
    have hc : angularCoordinates (SelbergMaassMean.point w.1 w.2)=![w.1,w.2] := by
      ext i; fin_cases i <;> simp [angularCoordinates,SelbergMaassMean.point]
    rw [hc] at hh
    exact hh
  have hs : (∫ y in SelbergModularDomainSlices.arcFloor..Y,
      (L ∘ F 0) (SelbergMaassMean.point (1/2) y)-(L ∘ F 0) (SelbergMaassMean.point (-(1/2)) y))=0 := by
    trans ∫ y in SelbergModularDomainSlices.arcFloor..Y,(0:ℝ)
    · apply intervalIntegral.integral_congr
      intro y hy
      have hf : SelbergModularDomainSlices.arcFloor ≤ Y :=
        (SelbergModularDomainSlices.arcHeight_le_one ⟨by norm_num,le_rfl⟩).trans hY
      have hyI : y ∈ Icc SelbergModularDomainSlices.arcFloor Y := by
        simpa only [uIcc_of_le hf] using hy
      have hy0 := SelbergModularDomainSlices.arcFloor_pos.trans_le hyI.1
      simp only [Function.comp_apply,F,planarFlux_point,original_side_cancellation q r d hy0,sub_self]
    · exact intervalIntegral.integral_zero
  have ha : (∫ x in (0:ℝ)..1/2,SelbergModularCurrentGreen.normalPair (L ∘ F 0) (L ∘ F 1) x)=0 := by
    trans ∫ x in (0:ℝ)..1/2,(0:ℝ)
    · apply intervalIntegral.integral_congr
      intro x hx
      have hxI : x ∈ Icc (0:ℝ) (1/2) := by simpa using hx
      have hxF : x ∈ Icc (-(1/2:ℝ)) (1/2) := ⟨by linarith [hxI.1],hxI.2⟩
      have hy0 := SelbergMaassTraceStokes.arcHeight_pos hxF
      have hc := congrArg L (original_arc_cancellation q r d (x := x) hy0
        (by rw [SelbergMaassTraceStokes.arcHeight_sq hxF]; ring))
      have hscale (a : ℝ) (b : ℂ) : L ((a:ℂ)*b)=a*L b := by
        simpa only [Complex.real_smul,smul_eq_mul] using L.map_smul a b
      simp only [map_sub,map_zero,hscale] at hc
      simp only [SelbergModularCurrentGreen.normalPair,Function.comp_apply,F,planarFlux_point]
      linear_combination hc
    · exact intervalIntegral.integral_zero
  rw [hd,hs,ha,zero_add,add_zero] at h
  simpa only [Function.comp_apply,F,planarFlux_point] using h

/-- The complete original angular action on the actual curved modular domain leaves only its top flux. -/
theorem original_modular_area (q r : XiZeroCopy) (d : ℝ)
    {Y : ℝ} (hY : 1 ≤ Y) :
    (∫ w in SelbergModularDomainSlices.domain Y,
      defect (circleField q d) (physicalAngularParameter r) ![w.1,w.2])=
      normalFlux q r d Y := by
  have hL (L : ℂ →L[ℝ] ℝ) :
      L (∫ w in SelbergModularDomainSlices.domain Y,
        defect (circleField q d) (physicalAngularParameter r) ![w.1,w.2])=
      L (∫ x in (-(1/2:ℝ))..1/2,
        flux (circleField q d) (physicalAngularParameter r) 1 ![x,Y]) := by
    rw [← L.integral_comp_comm (defect_integrable q r d Y),
      ← L.intervalIntegral_comp_comm (flux_integrable q r d Y (by linarith))]
    exact projected_area q r d L hY
  exact Complex.ext (hL Complex.reCLM) (hL Complex.imCLM)


end RHTower.D4BMOriginalCircleGreen
end

open Set Filter Topology MeasureTheory UpperHalfPlane
open scoped ContDiff
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal
attribute [-instance] RCLike.innerProductSpace
namespace RHTower.D4BMOriginalCirclePeriod
open D4BMCausalKernel D4BMModularCore D4BMGlobalAngularResponse D4BMNativeCircle D4BMJointSource
private def kernelFlux (nu : ℂ) (z : ℝ) : ℝ :=
  (((z:ℂ)^(2 : ℕ)-1)*star (legendreKernel nu z)*legendreKernelFirst nu z).im

private theorem kernelFlux_derivative (nu : ℂ) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (kernelFlux nu) ((nu*(nu+1)).im*Complex.normSq (legendreKernel nu z)) z := by
  obtain ⟨hP,hP1⟩ := legendreKernel_derivatives nu hz
  have hzD := ((hasDerivAt_id z).ofReal_comp.pow 2).sub_const (1:ℂ)
  have h := Complex.imCLM.hasFDerivAt.comp_hasDerivAt z ((hzD.mul hP.star).mul hP1)
  apply h.congr_deriv
  norm_num only [Complex.imCLM_apply, Pi.mul_apply, Pi.pow_apply, id_eq]
  simp only [pow_one, Complex.ofReal_one, mul_one]
  change ((2*(z:ℂ)*star (legendreKernel nu z)+((z:ℂ)^(2 : ℕ)-1)*star (legendreKernelFirst nu z))*legendreKernelFirst nu z
    +((z:ℂ)^(2 : ℕ)-1)*star (legendreKernel nu z)*legendreKernelSecond nu z).im =
    (nu*(nu+1)).im*Complex.normSq (legendreKernel nu z)
  have he := congrArg (fun w : ℂ => (star (legendreKernel nu z)*w).im)
    (legendreKernel_equation nu hz)
  simp only [pow_two, Complex.mul_im,Complex.mul_re,Complex.sub_re,Complex.sub_im,
    Complex.add_re,Complex.add_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.one_re,Complex.one_im,Complex.zero_re,Complex.zero_im,
    Complex.star_def,Complex.conj_re,Complex.conj_im,Complex.normSq_apply] at he ⊢
  linear_combination he

private theorem kernel_continuousOn (nu : ℂ) {Z : ℝ} :
    ContinuousOn (legendreKernel nu) (Icc 1 Z) := by
  intro z hz
  exact (legendreKernel_derivatives nu (lt_of_lt_of_le zero_lt_one hz.1)).1.continuousAt.continuousWithinAt

private theorem kernelFlux_integral (nu : ℂ) {Z : ℝ} (hZ : 1 ≤ Z) :
    kernelFlux nu Z=(nu*(nu+1)).im*∫ z in (1:ℝ)..Z, Complex.normSq (legendreKernel nu z) := by
  have hc : ContinuousOn (kernelFlux nu) (Icc 1 Z) := fun z hz =>
    (kernelFlux_derivative nu (lt_of_lt_of_le zero_lt_one hz.1)).continuousAt.continuousWithinAt
  have hn : ContinuousOn (fun z => Complex.normSq (legendreKernel nu z)) (Icc 1 Z) :=
    Complex.continuous_normSq.comp_continuousOn (kernel_continuousOn nu)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hZ hc
    (fun z hz => kernelFlux_derivative nu (lt_trans zero_lt_one hz.1))
    ((continuousOn_const.mul hn).intervalIntegrable_of_Icc hZ)
  have hzero : kernelFlux nu 1=0 := by simp [kernelFlux]
  rw [hzero,sub_zero,intervalIntegral.integral_const_mul] at hi
  exact hi.symm

private theorem kernel_ne_zero (nu : ℂ) (ha : (nu*(nu+1)).im ≠ 0)
    {Z : ℝ} (hZ : 1 ≤ Z) : legendreKernel nu Z ≠ 0 := by
  by_cases he : Z=1
  · rw [he,legendreKernel_one]
    exact one_ne_zero
  have hZ' : 1 < Z := lt_of_le_of_ne hZ (Ne.symm he)
  intro hzero
  have hf := kernelFlux_integral nu hZ
  have hz : kernelFlux nu Z=0 := by simp [kernelFlux,hzero]
  rw [hz] at hf
  have hn : ContinuousOn (fun z => Complex.normSq (legendreKernel nu z)) (Icc 1 Z) :=
    Complex.continuous_normSq.comp_continuousOn (kernel_continuousOn nu)
  have hp : 0 < ∫ z in (1:ℝ)..Z, Complex.normSq (legendreKernel nu z) := by
    have h := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt hZ'
      (f := fun _ => (0:ℝ)) continuousOn_const hn
      (fun z _ => Complex.normSq_nonneg _)
      ⟨1,⟨le_rfl,hZ⟩,by simp [legendreKernel_one]⟩
    simpa using h
  exact mul_ne_zero ha (ne_of_gt hp) hf.symm


def readerExponent (q : XiZeroCopy) : ℂ := 1-(q.1:ℂ)/2

def readerEigenvalue (q : XiZeroCopy) : ℂ := readerExponent q*(readerExponent q-1)

theorem readerEigenvalue_eq (q : XiZeroCopy) :
    readerEigenvalue q=physicalAngularParameter q^(2 : ℕ)-1/4 := by
  rw [physicalAngularParameter_eq]
  unfold readerEigenvalue readerExponent
  ring

theorem readerEigenvalue_nonreal (q : XiZeroCopy) : (readerEigenvalue q).im ≠ 0 := by
  have h := xi_divisor_support_im_ne_zero q.1
  have hr := (xi_divisor_support_re_mem_open_unit q.1).2
  have he : (readerEigenvalue q).im=((q.1:ℂ).re-1)*(q.1:ℂ).im/2 := by
    simp [readerEigenvalue,readerExponent,Complex.mul_im]
    ring
  rw [he]
  exact div_ne_zero (mul_ne_zero (sub_ne_zero.mpr (ne_of_lt hr)) h) (by norm_num)

theorem reader_powerCircle_ne_zero (q : XiZeroCopy) (d : ℝ) :
    powerCircle (readerExponent q) d ≠ 0 := by
  rw [powerCircle_eq_legendre]
  apply kernel_ne_zero _ _ (Real.one_le_cosh d)
  have he : -readerExponent q*(-readerExponent q+1)=readerEigenvalue q := by
    unfold readerEigenvalue
    ring
  rw [he]
  exact readerEigenvalue_nonreal q

end RHTower.D4BMOriginalCirclePeriod
end

open Set Filter Topology MeasureTheory UpperHalfPlane
open scoped ContDiff
open GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMOriginalCirclePeriod
open D4BMGlobalAngularResponse D4BMJointSource D4BMModularCore D4BMNativeCircle
open D4BMNativeCuspJets D4BMOriginalScalarRestoration D4BMOriginalCausalRestoration
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal
attribute [-instance] RCLike.innerProductSpace

def coefficient (q : XiZeroCopy) (d : ℝ) (i : Fin 3) : ℂ :=
  principalAmplitude q i*powerCircle (principalExponent q i) d

def cutoffResidual (q : XiZeroCopy) (d : ℝ) (z : UpperHalfPlane) : ℂ :=
  mean q d z.re (Real.log z.im)-
    ∑ i : Fin 3, coefficient q d i*cutoffPower (principalExponent q i) (coordinates z)

def period (q : XiZeroCopy) (d : ℝ) : ℂ :=
  (∫ z, scalar (physicalAngularParameter q) (coordinates z)*cutoffResidual q d z ∂measure)-
    ∑ i : Fin 3, scalarCutoffPeriod (physicalAngularParameter q) (principalExponent q i)/
      physicalAngularGap q q i*coefficient q d i


open GaloisForLFunctions.HTGeometry.ScalarTwoJet

def residualField (q : XiZeroCopy) (p : Fin 3 → ℝ) : ℂ :=
  mean q (p 0) (p 1) (p 2)-∑ i : Fin 3,
    coefficient q (p 0) i*powerCutoffHeight (principalExponent q i) (Real.exp (p 2))

private theorem circle_smooth (a : ℂ) : ContDiff ℝ ∞ (powerCircle a) := by
  apply contDiff_iff_contDiffAt.mpr
  intro d
  have h := (D4BMCausalSourceKernel.legendre_contDiffAt (-a) (Real.cosh_pos d)).comp d
    Real.contDiff_cosh.contDiffAt
  simpa only [Function.comp_def,← powerCircle_eq_legendre] using h

private theorem residualField_smooth (q : XiZeroCopy) : ContDiff ℝ ∞ (residualField q) := by
  have hm : ContDiff ℝ ∞ (fun p : Fin 3 → ℝ => mean q (p 0) (p 1) (p 2)) := by
    have hc : ContDiff ℝ ∞ (fun p : Fin 3 → ℝ => (p 0,p 1,p 2)) := by fun_prop
    have h := (D4BMNativeResponse.nativeMean_joint_smooth q).comp hc
    exact h
  apply hm.sub
  apply ContDiff.sum
  intro i _
  have hc : ContDiff ℝ ∞ (fun p : Fin 3 → ℝ => coefficient q (p 0) i) :=
    contDiff_const.mul ((circle_smooth _).comp (contDiff_apply ℝ ℝ (0:Fin 3)))
  exact hc.mul ((powerCutoffHeight_smooth _).comp
    (Real.contDiff_exp.comp (contDiff_apply ℝ ℝ (2:Fin 3))))

private theorem jet_smooth {f : (Fin 3 → ℝ) → ℂ} (hf : ContDiff ℝ ∞ f)
    (word : List (Fin 3)) : ContDiff ℝ ∞ (nativeJet word f) := by
  induction word with
  | nil => exact hf
  | cons i word ih => exact (ih.fderiv_right (by simp)).clm_apply contDiff_const

private theorem jet_germ {f g : (Fin 3 → ℝ) → ℂ} {p : Fin 3 → ℝ}
    (h : f =ᶠ[𝓝 p] g) (word : List (Fin 3)) :
    nativeJet word f =ᶠ[𝓝 p] nativeJet word g := by
  induction word with
  | nil => exact h
  | cons i word ih =>
    filter_upwards [ih.fderiv (𝕜 := ℝ)] with v hv
    exact congrArg (fun L => L (Pi.single i 1)) hv

private theorem residualField_high_germ (q : XiZeroCopy) (p : Fin 3 → ℝ)
    (hp : 3 < Real.exp (p 2)) :
    residualField q =ᶠ[𝓝 p] (fun v => cuspMeanRemainder q (v 0) (v 1) (v 2)) := by
  have hc : Continuous (fun v : Fin 3 → ℝ => Real.exp (v 2)) :=
    Real.continuous_exp.comp (continuous_apply 2)
  filter_upwards [(isOpen_lt continuous_const hc).mem_nhds hp] with v hv
  have hcut (i : Fin 3) : powerCutoffHeight (principalExponent q i) (Real.exp (v 2))=
      (Real.exp (v 2):ℂ)^principalExponent q i := by
    change (Real.smoothTransition (Real.exp (v 2)-2):ℂ)*(Real.exp (v 2):ℂ)^_= _
    rw [Real.smoothTransition.one_of_one_le (by linarith),Complex.ofReal_one,one_mul]
  simp only [residualField,cuspMeanRemainder,transportedPrincipal,hcut,coefficient]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Every actual mixed residual jet has a uniform height bound on a compact radius interval. -/
theorem residualJet_height_bound (q : XiZeroCopy) (word : List (Fin 3)) (D : Ici (0:ℝ)) :
    ∃ K : ℝ, ∀ d ∈ Icc (0:ℝ) D, ∀ z : UpperHalfPlane, z ∈ ModularGroup.fd →
      ‖(z.im:ℂ)*nativeJet word (residualField q) ![d,z.re,Real.log z.im]‖ ≤ K := by
  obtain ⟨B,hB,hb⟩ := nativeCuspJet_rapid_bound q word 1 D
  let M := max 4 (Real.exp D)
  have hc : Continuous (fun p : ℝ × UpperHalfPlane =>
      (p.2.im:ℂ)*nativeJet word (residualField q) ![p.1,p.2.re,Real.log p.2.im]) := by
    have hm : Continuous (fun p : ℝ × UpperHalfPlane =>
        (![p.1,p.2.re,Real.log p.2.im] : Fin 3 → ℝ)) := by
      apply continuous_pi
      intro i
      fin_cases i
      · exact continuous_fst
      · exact UpperHalfPlane.continuous_re.comp continuous_snd
      · exact (UpperHalfPlane.continuous_im.comp continuous_snd).log (fun p => p.2.im_pos.ne')
    exact (Complex.continuous_ofReal.comp (UpperHalfPlane.continuous_im.comp continuous_snd)).mul
      ((jet_smooth (residualField_smooth q) word).continuous.comp hm)
  obtain ⟨A,hA⟩ := (isCompact_Icc.prod (truncated_cell_compact M)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨max A (B*Real.exp D),?_⟩
  intro d hd z hz
  by_cases hy : z.im ≤ M
  · exact (hA (d,z) ⟨hd,hz,hy⟩).trans (le_max_left _ _)
  · have hM : M < z.im := lt_of_not_ge hy
    have hy3 : 3 < z.im := by
      have hm := le_max_left (4:ℝ) (Real.exp D)
      dsimp [M] at hM
      linarith
    have hD : (D:ℝ) ≤ Real.log z.im := by
      apply Real.exp_le_exp.mp
      rw [Real.exp_log z.im_pos]
      exact (le_max_right _ _).trans hM.le
    have hh := hb d z.re (Real.log z.im) hd.1 hd.2 hD
    simp only [Nat.cast_one,one_mul] at hh
    have hj := (jet_germ (residualField_high_germ q ![d,z.re,Real.log z.im]
      (by simpa only [Matrix.cons_val,Real.exp_log z.im_pos] using hy3)) word).eq_of_nhds
    rw [hj,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos z.im_pos]
    calc
      z.im*‖nativeJet word (fun p => cuspMeanRemainder q (p 0) (p 1) (p 2))
        ![d,z.re,Real.log z.im]‖ ≤ z.im*(B*Real.exp ((D:ℝ)-Real.log z.im)) :=
          mul_le_mul_of_nonneg_left hh z.im_pos.le
      _ = B*Real.exp D := by rw [Real.exp_sub,Real.exp_log z.im_pos]; field_simp
      _ ≤ _ := le_max_right _ _

private theorem residualJet_continuous (q : XiZeroCopy) (word : List (Fin 3)) (d : ℝ) :
    Continuous (fun z : UpperHalfPlane => nativeJet word (residualField q) ![d,z.re,Real.log z.im]) := by
  have hc : Continuous (fun z : UpperHalfPlane => (![d,z.re,Real.log z.im] : Fin 3 → ℝ)) := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_const
    · exact UpperHalfPlane.continuous_re
    · exact UpperHalfPlane.continuous_im.log (fun z => z.im_pos.ne')
  exact (jet_smooth (residualField_smooth q) word).continuous.comp hc

theorem residualJet_height_memLp (q : XiZeroCopy) (word : List (Fin 3)) (d : Ici (0:ℝ)) :
    MemLp (fun z : UpperHalfPlane => (z.im:ℂ)*
      nativeJet word (residualField q) ![d,z.re,Real.log z.im]) 2 measure := by
  obtain ⟨K,hK⟩ := residualJet_height_bound q word d
  have hc := (Complex.continuous_ofReal.comp UpperHalfPlane.continuous_im).mul
    (residualJet_continuous q word d)
  apply MemLp.of_bound hc.aestronglyMeasurable K
  filter_upwards [ae_restrict_mem ModularGroup.isClosed_fd.measurableSet] with z hz
  exact hK d ⟨d.property,le_rfl⟩ z hz

theorem residualJet_scalar_integrable (q : XiZeroCopy) (word : List (Fin 3)) (d : Ici (0:ℝ)) :
    Integrable (fun z : UpperHalfPlane => scalar (physicalAngularParameter q) (coordinates z)*
      nativeJet word (residualField q) ![d,z.re,Real.log z.im]) measure := by
  have h := (physicalDualDensity_memLp q).integrable_mul (residualJet_height_memLp q word d)
  apply h.congr
  filter_upwards with z
  change ((z.im:ℂ)⁻¹*scalar (physicalAngularParameter q) (coordinates z))*
    ((z.im:ℂ)*nativeJet word (residualField q) ![d,z.re,Real.log z.im])=_
  field_simp [Complex.ofReal_ne_zero.mpr z.im_pos.ne']

theorem cutoffResidual_scalar_integrable (q : XiZeroCopy) (d : Ici (0:ℝ)) :
    Integrable (fun z : UpperHalfPlane => scalar (physicalAngularParameter q) (coordinates z)*
      cutoffResidual q d z) measure := by
  have h := residualJet_scalar_integrable q [] d
  convert h using 1
  funext z
  simp only [nativeJet,residualField,Matrix.cons_val,Real.exp_log z.im_pos,cutoffResidual,
    powerCutoffHeight,cutoffPower,coordinates,cutoff]

theorem original_circle_finitePart (q : XiZeroCopy) (d : Ici (0:ℝ)) :
    Tendsto (fun Y => truncatedIntegral (fun z =>
      scalar (physicalAngularParameter q) (coordinates z)*mean q d z.re (Real.log z.im)) Y-
        principalCounterterm q (coefficient q d) Y) atTop (𝓝 (period q d)) := by
  have h := integrable_residual_restoration q (cutoffResidual q d) (coefficient q d)
    (cutoffResidual_scalar_integrable q d)
  simp only [cutoffResidual,sub_add_cancel] at h
  exact h

theorem period_zero (q : XiZeroCopy) : period q 0=physicalSelfSourceCoefficient q := by
  have hc : coefficient q 0=principalAmplitude q := by
    funext i
    simp only [coefficient,powerCircle_eq_legendre,Real.cosh_zero,D4BMCausalKernel.legendreKernel_one,
      mul_one]
  have h := original_circle_finitePart q ⟨0,by simp⟩
  simp only [hc,mean_zero] at h
  apply tendsto_nhds_unique h
  convert original_square_finitePart q using 1
  funext Y
  have he (z : UpperHalfPlane) : ![z.re, Real.exp (Real.log z.im)] = coordinates z := by
    rw [Real.exp_log z.im_pos]
    rfl
  simp only [he]

private theorem residualJet_radius_hasDerivAt (q : XiZeroCopy) (word : List (Fin 3))
    (x k d : ℝ) :
    HasDerivAt (fun t => nativeJet word (residualField q) ![t,x,k])
      (nativeJet (0::word) (residualField q) ![d,x,k]) d := by
  have hi : HasDerivAt (fun t : ℝ => (![t,x,k] : Fin 3 → ℝ)) (Pi.single 0 1) d := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · simpa using! hasDerivAt_id d
    · simpa using! hasDerivAt_const d x
    · simpa using! hasDerivAt_const d k
  have hf := ((jet_smooth (residualField_smooth q) word).differentiable (by simp) ![d,x,k]).hasFDerivAt
  exact hf.comp_hasDerivAt d hi

/-- Actual scalar-reader integrals of mixed jets of the original three-power residual. -/
def residualPeriodJet (q : XiZeroCopy) (word : List (Fin 3)) (d : ℝ) : ℂ :=
  ∫ z : UpperHalfPlane, scalar (physicalAngularParameter q) (coordinates z)*
    nativeJet word (residualField q) ![d,z.re,Real.log z.im] ∂measure

/-- Differentiation is admitted by the actual original-field cusp bounds, not a supplied hypothesis. -/
theorem residualPeriodJet_hasDerivAt (q : XiZeroCopy) (word : List (Fin 3)) (d : ℝ) (hd : 0 < d) :
    HasDerivAt (residualPeriodJet q word) (residualPeriodJet q (0::word) d) d := by
  let D : Ici (0:ℝ) := ⟨d+1,by change 0 ≤ d+1; linarith⟩
  obtain ⟨K,hK⟩ := residualJet_height_bound q (0::word) D
  let F (x : ℝ) (z : UpperHalfPlane) := scalar (physicalAngularParameter q) (coordinates z)*
    nativeJet word (residualField q) ![x,z.re,Real.log z.im]
  let F' (x : ℝ) (z : UpperHalfPlane) := scalar (physicalAngularParameter q) (coordinates z)*
    nativeJet (0::word) (residualField q) ![x,z.re,Real.log z.im]
  have hs : Ioo (0:ℝ) D ∈ 𝓝 d := isOpen_Ioo.mem_nhds ⟨hd,by change d < d+1; linarith⟩
  have hmeas : ∀ᶠ x in 𝓝 d, AEStronglyMeasurable (F x) measure := by
    filter_upwards [hs] with x hx
    exact (residualJet_scalar_integrable q word ⟨x,hx.1.le⟩).aestronglyMeasurable
  have hbound : ∀ᵐ z ∂measure, ∀ x ∈ Ioo (0:ℝ) D,
      ‖F' x z‖ ≤ K*‖physicalDualDensity q z‖ := by
    filter_upwards [ae_restrict_mem ModularGroup.isClosed_fd.measurableSet] with z hz
    intro x hx
    have he : F' x z = physicalDualDensity q z*((z.im:ℂ)*
        nativeJet (0::word) (residualField q) ![x,z.re,Real.log z.im]) := by
      dsimp [F',physicalDualDensity]
      field_simp [Complex.ofReal_ne_zero.mpr z.im_pos.ne']
    rw [he,norm_mul,mul_comm K]
    exact mul_le_mul_of_nonneg_left (hK x ⟨hx.1.le,hx.2.le⟩ z hz) (norm_nonneg _)
  have hint : Integrable (fun z => K*‖physicalDualDensity q z‖) measure :=
    ((MemLp.integrable (by norm_num) (physicalDualDensity_memLp q)).norm).const_mul K
  have hdiff : ∀ᵐ z ∂measure, ∀ x ∈ Ioo (0:ℝ) D, HasDerivAt (F · z) (F' x z) x := by
    filter_upwards with z
    intro x _
    exact (residualJet_radius_hasDerivAt q word z.re (Real.log z.im) x).const_mul _
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hs hmeas
    (residualJet_scalar_integrable q word ⟨d,hd.le⟩)
    (residualJet_scalar_integrable q (0::word) ⟨d,hd.le⟩).aestronglyMeasurable hbound hint hdiff).2

private theorem residualJet_scalar_bound (q : XiZeroCopy) (word : List (Fin 3)) (D : Ici (0:ℝ)) :
    ∃ K : ℝ, (Integrable (fun z => K*‖physicalDualDensity q z‖) measure) ∧
      ∀ᵐ z ∂measure, ∀ x ∈ Icc (0:ℝ) D,
        ‖scalar (physicalAngularParameter q) (coordinates z)*
          nativeJet word (residualField q) ![x,z.re,Real.log z.im]‖ ≤ K*‖physicalDualDensity q z‖ := by
  obtain ⟨K,hK⟩ := residualJet_height_bound q word D
  refine ⟨K,((MemLp.integrable (by norm_num) (physicalDualDensity_memLp q)).norm).const_mul K,?_⟩
  filter_upwards [ae_restrict_mem ModularGroup.isClosed_fd.measurableSet] with z hz
  intro x hx
  have he : scalar (physicalAngularParameter q) (coordinates z)*
      nativeJet word (residualField q) ![x,z.re,Real.log z.im]=
      physicalDualDensity q z*((z.im:ℂ)*nativeJet word (residualField q) ![x,z.re,Real.log z.im]) := by
    dsimp [physicalDualDensity]
    field_simp [Complex.ofReal_ne_zero.mpr z.im_pos.ne']
  rw [he,norm_mul,mul_comm K]
  exact mul_le_mul_of_nonneg_left (hK x hx z hz) (norm_nonneg _)

/-- Every restored jet period is right-continuous at the original radius-zero datum. -/
theorem residualPeriodJet_continuousAt_zero (q : XiZeroCopy) (word : List (Fin 3)) :
    ContinuousWithinAt (residualPeriodJet q word) (Ici (0:ℝ)) 0 := by
  obtain ⟨K,hint,hK⟩ := residualJet_scalar_bound q word ⟨1,by norm_num⟩
  have hs : ∀ᶠ x : ℝ in 𝓝[Ici 0] 0, x ∈ Icc (0:ℝ) 1 := by
    have h1 : ∀ᶠ x : ℝ in 𝓝 (0:ℝ), x < 1 := Iio_mem_nhds (by norm_num)
    filter_upwards [self_mem_nhdsWithin,h1.filter_mono nhdsWithin_le_nhds] with x hx hx1
    exact ⟨hx,hx1.le⟩
  apply tendsto_integral_filter_of_dominated_convergence (fun z => K*‖physicalDualDensity q z‖)
  · filter_upwards [hs] with x hx
    exact (residualJet_scalar_integrable q word ⟨x,hx.1⟩).aestronglyMeasurable
  · filter_upwards [hs] with x hx
    filter_upwards [hK] with z hz
    exact hz x hx
  · exact hint
  · filter_upwards with z
    exact ((residualJet_radius_hasDerivAt q word z.re (Real.log z.im) 0).const_mul
      (scalar (physicalAngularParameter q) (coordinates z))).continuousAt.mono_left nhdsWithin_le_nhds

def correction (q : XiZeroCopy) (d : ℝ) : ℂ :=
  ∑ i : Fin 3, scalarCutoffPeriod (physicalAngularParameter q) (principalExponent q i)/
    physicalAngularGap q q i*coefficient q d i

private theorem correction_smooth (q : XiZeroCopy) : ContDiff ℝ ∞ (correction q) := by
  apply ContDiff.sum
  intro i _
  exact contDiff_const.mul (contDiff_const.mul (circle_smooth _))

theorem period_eq_residualJet_sub (q : XiZeroCopy) (d : ℝ) :
    period q d=residualPeriodJet q [] d-correction q d := by
  unfold period residualPeriodJet correction
  congr 1
  apply integral_congr_ae
  filter_upwards with z
  simp only [nativeJet,residualField,Matrix.cons_val,Real.exp_log z.im_pos,cutoffResidual,
    powerCutoffHeight,cutoffPower,coordinates,cutoff]

theorem period_continuousAt_zero (q : XiZeroCopy) :
    ContinuousWithinAt (period q) (Ici (0:ℝ)) 0 := by
  have he : period q=fun d => residualPeriodJet q [] d-correction q d :=
    funext (period_eq_residualJet_sub q)
  rw [he]
  exact (residualPeriodJet_continuousAt_zero q []).sub
    (correction_smooth q).continuous.continuousAt.continuousWithinAt

/-- The first radius derivative of the actual finite part, with all three original corrections. -/
theorem period_hasDerivAt (q : XiZeroCopy) (d : ℝ) (hd : 0 < d) :
    HasDerivAt (period q) (residualPeriodJet q [0] d-deriv (correction q) d) d := by
  have he : period q=fun d => residualPeriodJet q [] d-correction q d :=
    funext (period_eq_residualJet_sub q)
  rw [he]
  exact (residualPeriodJet_hasDerivAt q [] d hd).sub
    ((correction_smooth q).differentiable (by simp) d).hasDerivAt

/-- The second radius derivative is again the original integral and differentiated corrections. -/
theorem period_deriv_hasDerivAt (q : XiZeroCopy) (d : ℝ) (hd : 0 < d) :
    HasDerivAt (deriv (period q))
      (residualPeriodJet q [0,0] d-deriv (deriv (correction q)) d) d := by
  have he : deriv (period q) =ᶠ[𝓝 d]
      (fun x => residualPeriodJet q [0] x-deriv (correction q) x) := by
    filter_upwards [Ioi_mem_nhds hd] with x hx
    exact (period_hasDerivAt q x hx).deriv
  exact ((residualPeriodJet_hasDerivAt q [0] d hd).sub
    (((contDiff_infty_iff_deriv.mp (correction_smooth q)).2).differentiable (by simp) d).hasDerivAt).congr_of_eventuallyEq he

end
end RHTower.D4BMOriginalCirclePeriod
