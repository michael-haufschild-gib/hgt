import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalCuspFlux
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhysicalCoreCutoff
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMModularCoexact
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMModularLaplacian
import GaloisForLFunctions.RHTower.SelbergModularCurrentGreen

/-!
# Physical coexact pairing with the complete original causal scalar

The actual covector pairing differs from minus the scalar-reader eigenvalue
 times the hyperbolic scalar period by its original normal boundary flux.
Both vertical sides and the complete curved modular core are retained before
cancellation. This is the normalization required to compare the original
physical current with its scalar projection. The derived nonconstant cusp
powers leave precisely the independent-reader constant, zero for the diagonal
and reflected readers. No temporal or horizon limit is interchanged.
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
namespace RHTower.D4BMOriginalScalarPairing
open GaloisForLFunctions.HTGeometry ScalarTwoJet D4BMHorizon D4BMModularCore
open D4BMOriginalCausalPotential D4BMOriginalAngularGreen D4BMJointSource
open D4BMGlobalAngularResponse

private theorem source_smooth (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (p v : ℝ)
    (z : Point) (hz : 0 < z 1) : ContDiffAt ℝ ∞ (D4BMOriginalAngularGreen.source q branch amp p v) z := by
  have hc : ContDiffAt ℝ ∞ (fun w : Point => (w 0,Real.log (w 1))) z :=
    (contDiff_apply ℝ ℝ (0:Fin 2)).contDiffAt.prodMk
      ((contDiff_apply ℝ ℝ (1:Fin 2)).contDiffAt.log hz.ne')
  have h := (originalPotential_angular_smooth q branch amp p v).contDiffAt.comp z hc
  exact h

private theorem reader_smooth (q : XiZeroCopy) (z : Point) (hz : 0 < z 1) :
    ContDiffAt ℝ ∞ (D4BMLiteralCusp.scalar (physicalAngularParameter q)) z :=
  (D4BMAngularSeries.cuspLeg_contDiffOn .scalar (physicalAngularParameter q)).contDiffAt
    ((isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hz)

private theorem source_modular (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (p v : ℝ)
    (A : SL(2,ℤ)) (z : UpperHalfPlane) :
    D4BMOriginalAngularGreen.source q branch amp p v (coordinates (A • z)) = D4BMOriginalAngularGreen.source q branch amp p v (coordinates z) :=
  originalPotential_modular q branch amp p v A z

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
    differential F z v=differential F (A • z) ((1/(denom A z)^2)*v) := by
  have he : (fun w : UpperHalfPlane => F (coordinates (A • w))) =
      (fun w => F (coordinates w)) := funext hi
  have h := chart_fderiv_modular_pullback A (fun w => F (coordinates w))
    (chartSmooth_coordinates F hF) z
  rw [he] at h
  unfold differential
  rw [h,ContinuousLinearMap.comp_apply,modular_chart_jacobian]

/-- The original scalar-density pairing in the hyperbolic area measure. -/
def scalarDensity (F : Point → ℂ) (u : ℂ) (z : Point) : ℂ :=
  F z*D4BMLiteralCusp.scalar u z/(z 1:ℂ)^2

/-- The actual coexact source tested by the original physical covector. -/
def coexactPair (F : Point → ℂ) (u : ℂ) (z : Point) : ℂ :=
  ∑ j : Fin 2, coexact F j z*D4BMLiteralCusp.vector u j z

/-- Normal boundary term required when transferring the source's angular derivative. -/
def flux (F : Point → ℂ) (u : ℂ) (j : Fin 2) (z : Point) : ℂ :=
  F z*coordDeriv j (D4BMLiteralCusp.scalar u) z

def defect (F : Point → ℂ) (u : ℂ) (z : Point) : ℂ :=
  coexactPair F u z+(u^2-1/4)*scalarDensity F u z

private theorem partial_smooth {F : Point → ℂ} {z : Point} (hF : ContDiffAt ℝ ∞ F z) (j : Fin 2) :
    ContDiffAt ℝ ∞ (coordDeriv j F) z := coordDeriv_contDiffAt hF (by simp) j

private theorem divergence_flux {F : Point → ℂ} {z : Point} (hF : ContDiffAt ℝ ∞ F z)
    (hz : 0<z 1) (u : ℂ) :
    (∑ j : Fin 2, coordDeriv j (flux F u j) z)=defect F u z := by
  have hS : ContDiffAt ℝ ∞ (D4BMLiteralCusp.scalar u) z :=
    (D4BMAngularSeries.cuspLeg_contDiffOn .scalar u).contDiffAt
      ((isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hz)
  have hd (j : Fin 2) : coordDeriv j (flux F u j) z=
      coordDeriv j F z*coordDeriv j (D4BMLiteralCusp.scalar u) z+
        F z*coordDeriv j (coordDeriv j (D4BMLiteralCusp.scalar u)) z :=
    coordDeriv_mul (hF.differentiableAt (by simp))
      ((partial_smooth hS j).differentiableAt (by simp)) j
  have he := D4BMLiteralCusp.scalar_equation u z hz
  rw [scalarLaplacian_eq _ z hz] at he
  simp only [D4BMLiteralCusp.scalarQ,neg_sub] at he
  have hl : coordDeriv 0 (coordDeriv 0 (D4BMLiteralCusp.scalar u)) z+
      coordDeriv 1 (coordDeriv 1 (D4BMLiteralCusp.scalar u)) z=
        (u^2-1/4)*D4BMLiteralCusp.scalar u z/(z 1:ℂ)^2 := by
    apply (eq_div_iff (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr hz.ne'))).mpr
    simpa only [mul_comm] using he
  calc
    _ = coexactPair F u z+F z*(coordDeriv 0 (coordDeriv 0 (D4BMLiteralCusp.scalar u)) z+
        coordDeriv 1 (coordDeriv 1 (D4BMLiteralCusp.scalar u)) z) := by
      simp only [Fin.sum_univ_two,hd,coexactPair,D4BMLiteralCusp.vector,coexact,
        Matrix.cons_val_zero,Matrix.cons_val_one]
      ring
    _ = defect F u z := by
      rw [hl]
      unfold defect scalarDensity
      ring

/-- The complete original top normal flux at a finite modular cusp cutoff. -/
def normalFlux (q r : XiZeroCopy) (branch : Bool) (amp : ℂ) (p v Y : ℝ) : ℂ :=
  ∫ X in (-(1/2:ℝ))..1/2,
    flux (D4BMOriginalAngularGreen.source q branch amp p v) (physicalAngularParameter r) 1 ![X,Y]

/-- Contraction of the original transfer flux with an arbitrary real tangent direction. -/
def current (q r : XiZeroCopy) (branch : Bool) (amp : ℂ) (p v : ℝ)
    (z : UpperHalfPlane) (a : ℂ) : ℂ :=
  (a.re:ℂ)*flux (D4BMOriginalAngularGreen.source q branch amp p v) (physicalAngularParameter r) 0 (coordinates z)+
    (a.im:ℂ)*flux (D4BMOriginalAngularGreen.source q branch amp p v) (physicalAngularParameter r) 1 (coordinates z)

private theorem current_differential (q r : XiZeroCopy) (branch : Bool) (amp : ℂ) (p v : ℝ)
    (z : UpperHalfPlane) (a : ℂ) :
    current q r branch amp p v z a =
      D4BMOriginalAngularGreen.source q branch amp p v (coordinates z)*
        differential (D4BMLiteralCusp.scalar (physicalAngularParameter r)) z a := by
  rw [differential_components]
  unfold current flux
  ring

/-- The source value and reader differential give their original modular normal current. -/
theorem current_modular (q r : XiZeroCopy) (branch : Bool) (amp : ℂ) (p v : ℝ)
    (A : SL(2,ℤ)) (z : UpperHalfPlane) (a : ℂ) :
    current q r branch amp p v z a =
      current q r branch amp p v (A • z) ((1/(denom A z)^2)*a) := by
  rw [current_differential,current_differential,source_modular,
    differential_modular _ (reader_smooth r) A (physicalScalar_modular r A)]

/-- The actual radial current reverses sign under inversion, including all causal and Fourier tails. -/
theorem current_radial_inversion (q r : XiZeroCopy) (branch : Bool) (amp : ℂ) (p v : ℝ)
    (z : UpperHalfPlane) :
    current q r branch amp p v z (z:ℂ)+
      current q r branch amp p v (S • z) ((S • z:UpperHalfPlane):ℂ)=0 := by
  have h := current_modular q r branch amp p v S z (z:ℂ)
  have hv : (1/(denom S z)^2)*(z:ℂ) = -((S • z:UpperHalfPlane):ℂ) := by
    simp only [UpperHalfPlane.modular_S_smul]
    simp [denom,ModularGroup.S,inv_neg]
    field_simp
  rw [hv] at h
  have hn : current q r branch amp p v (S • z) (-((S • z:UpperHalfPlane):ℂ)) =
      -current q r branch amp p v (S • z) ((S • z:UpperHalfPlane):ℂ) := by
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
theorem original_side_cancellation (q r : XiZeroCopy) (branch : Bool) (amp : ℂ) (p v : ℝ)
    {y : ℝ} (hy : 0 < y) :
    flux (D4BMOriginalAngularGreen.source q branch amp p v) (physicalAngularParameter r) 0 ![1/2,y]=
      flux (D4BMOriginalAngularGreen.source q branch amp p v) (physicalAngularParameter r) 0 ![-(1/2),y] := by
  have h := current_modular q r branch amp p v T
    (ofComplex (GaloisForLFunctions.RHTower.SelbergMaassMean.point (-(1/2)) y)) 1
  rw [GaloisForLFunctions.RHTower.SelbergMaassTraceBoundary.translation_point _ hy,
    show -(1/2:ℝ)+1=1/2 by ring] at h
  simpa [current,denom,ModularGroup.T,coordinates_point _ hy] using h.symm

/-- Literal oriented unit-circle fluxes cancel for the complete original source and reader. -/
theorem original_arc_cancellation (q r : XiZeroCopy) (branch : Bool) (amp : ℂ) (p v : ℝ)
    {x y : ℝ} (hy : 0 < y) (hxy : x^2+y^2=1) :
    ((x/y:ℝ):ℂ)*(flux (D4BMOriginalAngularGreen.source q branch amp p v) (physicalAngularParameter r) 0 ![-x,y]-
      flux (D4BMOriginalAngularGreen.source q branch amp p v) (physicalAngularParameter r) 0 ![x,y])-
      flux (D4BMOriginalAngularGreen.source q branch amp p v) (physicalAngularParameter r) 1 ![-x,y]-
      flux (D4BMOriginalAngularGreen.source q branch amp p v) (physicalAngularParameter r) 1 ![x,y]=0 := by
  let z := ofComplex (GaloisForLFunctions.RHTower.SelbergMaassMean.point x y)
  have h := current_radial_inversion q r branch amp p v z
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


private theorem flux_smooth (q r : XiZeroCopy) (branch : Bool) (amp : ℂ) (p v : ℝ)
    (j : Fin 2) (z : Point) (hz : 0 < z 1) :
    ContDiffAt ℝ ∞ (flux (D4BMOriginalAngularGreen.source q branch amp p v) (physicalAngularParameter r) j) z := by
  have hZ := source_smooth q branch amp p v z hz
  have hS := reader_smooth r z hz
  exact hZ.mul (partial_smooth hS j)

private def planarFlux (q r : XiZeroCopy) (branch : Bool) (amp : ℂ) (p v : ℝ)
    (j : Fin 2) : ℂ → ℂ :=
  flux (D4BMOriginalAngularGreen.source q branch amp p v) (physicalAngularParameter r) j ∘ angularCoordinates

private theorem planarFlux_smooth (q r : XiZeroCopy) (branch : Bool) (amp : ℂ) (p v : ℝ)
    (j : Fin 2) : ContDiffOn ℝ ∞ (planarFlux q r branch amp p v j) {z : ℂ | 0 < z.im} := by
  intro z hz
  exact ((flux_smooth q r branch amp p v j (angularCoordinates z) hz).comp z
    angularCoordinates.contDiff.contDiffAt).contDiffWithinAt

private theorem planarFlux_point (q r : XiZeroCopy) (branch : Bool) (amp : ℂ) (p v : ℝ)
    (j : Fin 2) (x y : ℝ) :
    planarFlux q r branch amp p v j (GaloisForLFunctions.RHTower.SelbergMaassMean.point x y)=
      flux (D4BMOriginalAngularGreen.source q branch amp p v) (physicalAngularParameter r) j ![x,y] := by
  have hp : angularCoordinates (GaloisForLFunctions.RHTower.SelbergMaassMean.point x y)=![x,y] := by
    ext i
    fin_cases i <;> simp [angularCoordinates,GaloisForLFunctions.RHTower.SelbergMaassMean.point]
  exact congrArg (flux (D4BMOriginalAngularGreen.source q branch amp p v) (physicalAngularParameter r) j) hp

private theorem projected_derivative (q r : XiZeroCopy) (branch : Bool) (amp : ℂ) (p v : ℝ)
    (j i : Fin 2) (L : ℂ →L[ℝ] ℝ) (z : ℂ) (hz : 0 < z.im) :
    fderiv ℝ (L ∘ planarFlux q r branch amp p v j) z (direction i)=
      L (coordDeriv i (flux (D4BMOriginalAngularGreen.source q branch amp p v)
        (physicalAngularParameter r) j) (angularCoordinates z)) := by
  have hf := ((planarFlux_smooth q r branch amp p v j).contDiffAt
    (isOpen_upperHalfPlaneSet.mem_nhds hz)).differentiableAt (by simp)
  rw [(L.hasFDerivAt.comp z hf.hasFDerivAt).fderiv,ContinuousLinearMap.comp_apply]
  exact congrArg L (angularCoordinates_derivative _ i z)

private theorem projected_divergence (q r : XiZeroCopy) (branch : Bool) (amp : ℂ) (p v : ℝ)
    (L : ℂ →L[ℝ] ℝ) (z : ℂ) (hz : 0 < z.im) :
    fderiv ℝ (L ∘ planarFlux q r branch amp p v 0) z 1+
      fderiv ℝ (L ∘ planarFlux q r branch amp p v 1) z Complex.I=
    L (defect (D4BMOriginalAngularGreen.source q branch amp p v) (physicalAngularParameter r) (angularCoordinates z)) := by
  have h0 := projected_derivative q r branch amp p v 0 0 L z hz
  have h1 := projected_derivative q r branch amp p v 1 1 L z hz
  simp only [direction,Matrix.cons_val_zero,Matrix.cons_val_one] at h0 h1
  rw [h0,h1,← map_add]
  congr 1
  simpa only [Fin.sum_univ_two] using
    divergence_flux (source_smooth q branch amp p v (angularCoordinates z) hz) hz (physicalAngularParameter r)

open GaloisForLFunctions.RHTower

private theorem defect_continuous (q r : XiZeroCopy) (branch : Bool) (amp : ℂ) (p v : ℝ) :
    ContinuousOn (defect (D4BMOriginalAngularGreen.source q branch amp p v) (physicalAngularParameter r))
      {z : Point | 0 < z 1} := by
  have hd : ContinuousOn (fun z : Point =>
      coordDeriv 0 (flux (D4BMOriginalAngularGreen.source q branch amp p v) (physicalAngularParameter r) 0) z+
      coordDeriv 1 (flux (D4BMOriginalAngularGreen.source q branch amp p v) (physicalAngularParameter r) 1) z)
      {z : Point | 0 < z 1} := by
    intro z hz
    exact ((partial_smooth (flux_smooth q r branch amp p v 0 z hz) 0).continuousAt.add
      (partial_smooth (flux_smooth q r branch amp p v 1 z hz) 1).continuousAt).continuousWithinAt
  apply hd.congr
  intro z hz
  simpa only [Fin.sum_univ_two] using
    (divergence_flux (source_smooth q branch amp p v z hz) hz (physicalAngularParameter r)).symm

private theorem defect_integrable (q r : XiZeroCopy) (branch : Bool) (amp : ℂ) (p v Y : ℝ) :
    IntegrableOn (fun w : ℝ × ℝ => defect (D4BMOriginalAngularGreen.source q branch amp p v)
      (physicalAngularParameter r) ![w.1,w.2]) (SelbergModularDomainSlices.domain Y) := by
  have hc : ContinuousOn (fun w : ℝ × ℝ => defect (D4BMOriginalAngularGreen.source q branch amp p v)
      (physicalAngularParameter r) ![w.1,w.2]) (SelbergModularDomainSlices.cell Y) := by
    apply (defect_continuous q r branch amp p v).comp
      (show Continuous (fun w : ℝ × ℝ => (![w.1,w.2] : Point)) by
        apply continuous_pi; intro i; fin_cases i <;> fun_prop).continuousOn
    intro w hw
    change 0 < w.2
    linarith [hw.2.1]
  exact (hc.mono (SelbergModularDomainSlices.domain_subset_cell Y)).integrableOn_compact
    (SelbergModularDomainSlices.isCompact_domain Y)

private theorem scalarDensity_continuous (q r : XiZeroCopy) (branch : Bool) (amp : ℂ) (p v : ℝ) :
    ContinuousOn (scalarDensity (D4BMOriginalAngularGreen.source q branch amp p v)
      (physicalAngularParameter r)) {z : Point | 0 < z 1} := by
  intro z hz
  have hn := (source_smooth q branch amp p v z hz).continuousAt.mul
    (reader_smooth r z hz).continuousAt
  have hd : ContinuousAt (fun w : Point => (w 1:ℂ)^2) z :=
    (Complex.ofRealCLM.continuous.continuousAt.comp (continuous_apply 1).continuousAt).pow 2
  exact (hn.div hd (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr hz.ne'))).continuousWithinAt

private theorem scalarDensity_integrable (q r : XiZeroCopy) (branch : Bool) (amp : ℂ) (p v Y : ℝ) :
    IntegrableOn (fun w : ℝ × ℝ => scalarDensity (D4BMOriginalAngularGreen.source q branch amp p v)
      (physicalAngularParameter r) ![w.1,w.2]) (SelbergModularDomainSlices.domain Y) := by
  have hc : ContinuousOn (fun w : ℝ × ℝ => scalarDensity (D4BMOriginalAngularGreen.source q branch amp p v)
      (physicalAngularParameter r) ![w.1,w.2]) (SelbergModularDomainSlices.cell Y) := by
    apply (scalarDensity_continuous q r branch amp p v).comp
      (show Continuous (fun w : ℝ × ℝ => (![w.1,w.2] : Point)) by
        apply continuous_pi; intro i; fin_cases i <;> fun_prop).continuousOn
    intro w hw
    change 0 < w.2
    linarith [hw.2.1]
  exact (hc.mono (SelbergModularDomainSlices.domain_subset_cell Y)).integrableOn_compact
    (SelbergModularDomainSlices.isCompact_domain Y)

private theorem coexactPair_integrable (q r : XiZeroCopy) (branch : Bool) (amp : ℂ) (p v Y : ℝ) :
    IntegrableOn (fun w : ℝ × ℝ => coexactPair (D4BMOriginalAngularGreen.source q branch amp p v)
      (physicalAngularParameter r) ![w.1,w.2]) (SelbergModularDomainSlices.domain Y) := by
  have h := (defect_integrable q r branch amp p v Y).sub
    ((scalarDensity_integrable q r branch amp p v Y).const_mul ((physicalAngularParameter r)^2-1/4))
  change IntegrableOn (fun w : ℝ × ℝ =>
    defect (D4BMOriginalAngularGreen.source q branch amp p v) (physicalAngularParameter r) ![w.1,w.2]-
      ((physicalAngularParameter r)^2-1/4)*
        scalarDensity (D4BMOriginalAngularGreen.source q branch amp p v) (physicalAngularParameter r) ![w.1,w.2])
    (SelbergModularDomainSlices.domain Y) at h
  simpa only [defect,add_sub_cancel_right] using h

private theorem flux_integrable (q r : XiZeroCopy) (branch : Bool) (amp : ℂ) (p v Y : ℝ)
    (hY : 0 < Y) : IntervalIntegrable (fun x : ℝ =>
      flux (D4BMOriginalAngularGreen.source q branch amp p v) (physicalAngularParameter r) 1 ![x,Y])
      volume (-(1/2:ℝ)) (1/2) := by
  have hmap : Continuous (fun x : ℝ => (![x,Y] : Point)) := by
    apply continuous_pi; intro i; fin_cases i <;> fun_prop
  apply Continuous.intervalIntegrable
  apply continuous_iff_continuousAt.mpr
  intro x
  exact (flux_smooth q r branch amp p v 1 ![x,Y] hY).continuousAt.comp
    (f := fun t : ℝ => (![t,Y] : Point)) (x := x) hmap.continuousAt

private theorem projected_area (q r : XiZeroCopy) (branch : Bool) (amp : ℂ) (p v : ℝ)
    (L : ℂ →L[ℝ] ℝ) {Y : ℝ} (hY : 1 ≤ Y) :
    (∫ w in SelbergModularDomainSlices.domain Y,
      L (defect (D4BMOriginalAngularGreen.source q branch amp p v) (physicalAngularParameter r) ![w.1,w.2]))=
      ∫ x in (-(1/2:ℝ))..1/2,
        L (flux (D4BMOriginalAngularGreen.source q branch amp p v) (physicalAngularParameter r) 1 ![x,Y]) := by
  let F := planarFlux q r branch amp p v
  have hF (j : Fin 2) : ContDiffOn ℝ 1 (L ∘ F j) {z : ℂ | 0 < z.im} :=
    L.contDiff.comp_contDiffOn ((contDiffOn_infty.mp (planarFlux_smooth q r branch amp p v j)) 1)
  have h := SelbergModularCurrentGreen.current_green_identity (L ∘ F 0) (hF 0)
    (L ∘ F 1) (hF 1) hY
  have hd : (∫ w in SelbergModularDomainSlices.domain Y,
      SelbergMaassTraceEnergy.dir 1 (L ∘ F 0) (SelbergMaassMean.point w.1 w.2)+
      SelbergMaassTraceEnergy.dir Complex.I (L ∘ F 1) (SelbergMaassMean.point w.1 w.2))=
      ∫ w in SelbergModularDomainSlices.domain Y,
        L (defect (D4BMOriginalAngularGreen.source q branch amp p v) (physicalAngularParameter r) ![w.1,w.2]) := by
    apply setIntegral_congr_fun (SelbergModularDomainSlices.isCompact_domain Y).measurableSet
    intro w hw
    have hw0 : 0 < w.2 := by linarith [hw.1.2.1]
    have hh := projected_divergence q r branch amp p v L (SelbergMaassMean.point w.1 w.2)
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
      simp only [Function.comp_apply,F,planarFlux_point,original_side_cancellation q r branch amp p v hy0,sub_self]
    · exact intervalIntegral.integral_zero
  have ha : (∫ x in (0:ℝ)..1/2,SelbergModularCurrentGreen.normalPair (L ∘ F 0) (L ∘ F 1) x)=0 := by
    trans ∫ x in (0:ℝ)..1/2,(0:ℝ)
    · apply intervalIntegral.integral_congr
      intro x hx
      have hxI : x ∈ Icc (0:ℝ) (1/2) := by simpa using hx
      have hxF : x ∈ Icc (-(1/2:ℝ)) (1/2) := ⟨by linarith [hxI.1],hxI.2⟩
      have hy0 := SelbergMaassTraceStokes.arcHeight_pos hxF
      have hc := congrArg L (original_arc_cancellation q r branch amp p v (x := x) hy0
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
theorem original_modular_area (q r : XiZeroCopy) (branch : Bool) (amp : ℂ) (p v : ℝ)
    {Y : ℝ} (hY : 1 ≤ Y) :
    (∫ w in SelbergModularDomainSlices.domain Y,
      defect (D4BMOriginalAngularGreen.source q branch amp p v) (physicalAngularParameter r) ![w.1,w.2])=
      normalFlux q r branch amp p v Y := by
  have hL (L : ℂ →L[ℝ] ℝ) :
      L (∫ w in SelbergModularDomainSlices.domain Y,
        defect (D4BMOriginalAngularGreen.source q branch amp p v) (physicalAngularParameter r) ![w.1,w.2])=
      L (∫ x in (-(1/2:ℝ))..1/2,
        flux (D4BMOriginalAngularGreen.source q branch amp p v) (physicalAngularParameter r) 1 ![x,Y]) := by
    rw [← L.integral_comp_comm (defect_integrable q r branch amp p v Y),
      ← L.intervalIntegral_comp_comm (flux_integrable q r branch amp p v Y (by linarith))]
    exact projected_area q r branch amp p v L hY
  exact Complex.ext (hL Complex.reCLM) (hL Complex.imCLM)

/-- The actual physical covector pairing has scalar projection factor `-mu`
and the complete original normal flux. This includes the curved modular core. -/
theorem original_physical_pairing (q r : XiZeroCopy) (branch : Bool) (amp : ℂ) (p v : ℝ)
    {Y : ℝ} (hY : 1 ≤ Y) :
    (∫ w in SelbergModularDomainSlices.domain Y,
      coexactPair (D4BMOriginalAngularGreen.source q branch amp p v) (physicalAngularParameter r) ![w.1,w.2])+
      ((physicalAngularParameter r)^2-1/4)*(∫ w in SelbergModularDomainSlices.domain Y,
        scalarDensity (D4BMOriginalAngularGreen.source q branch amp p v) (physicalAngularParameter r) ![w.1,w.2])=
      normalFlux q r branch amp p v Y := by
  have h := original_modular_area q r branch amp p v hY
  simp only [defect] at h
  rw [integral_add (coexactPair_integrable q r branch amp p v Y)
    ((scalarDensity_integrable q r branch amp p v Y).const_mul _),integral_const_mul] at h
  exact h

/-- The complete original physical pairing has its source-derived cusp subtraction.
The constant of an independent reader is retained; no time or horizon limit is interchanged. -/
theorem original_physical_pairing_finitePart (q r : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p v : Ici (0:ℝ)) :
    Tendsto (fun k : ℝ =>
      ((∫ w in SelbergModularDomainSlices.domain (Real.exp k),
        coexactPair (D4BMOriginalAngularGreen.source q branch amp p v) (physicalAngularParameter r) ![w.1,w.2])+
        ((physicalAngularParameter r)^2-1/4)*(∫ w in SelbergModularDomainSlices.domain (Real.exp k),
          scalarDensity (D4BMOriginalAngularGreen.source q branch amp p v) (physicalAngularParameter r) ![w.1,w.2]))-
        D4BMOriginalCuspFlux.pairingNonconstantFlux q r branch amp p v k) atTop
      (𝓝 (D4BMOriginalCuspFlux.pairingFluxConstant q r branch amp p v)) := by
  have h := D4BMOriginalCuspFlux.original_pairingCuspFlux_finitePart q r branch amp p v
  apply h.congr'
  filter_upwards [eventually_ge_atTop (0:ℝ)] with k hk
  rw [original_physical_pairing q r branch amp p v (Real.one_le_exp hk)]
  simp only [D4BMOriginalCuspFlux.pairingCuspFlux,normalFlux,
    D4BMOriginalCuspFlux.pairingFlux,flux,neg_div]

/-- The diagonal physical reader leaves zero combined pairing finite part,
with the actual nonconstant normal-flux powers subtracted. -/
theorem diagonal_physical_pairing_finitePart (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p v : Ici (0:ℝ)) :
    Tendsto (fun k : ℝ =>
      ((∫ w in SelbergModularDomainSlices.domain (Real.exp k),
        coexactPair (D4BMOriginalAngularGreen.source q branch amp p v) (physicalAngularParameter q) ![w.1,w.2])+
        ((physicalAngularParameter q)^2-1/4)*(∫ w in SelbergModularDomainSlices.domain (Real.exp k),
          scalarDensity (D4BMOriginalAngularGreen.source q branch amp p v) (physicalAngularParameter q) ![w.1,w.2]))-
        D4BMOriginalCuspFlux.pairingNonconstantFlux q q branch amp p v k) atTop (𝓝 0) := by
  simpa only [(D4BMOriginalCuspFlux.pairingFluxConstant_original_readers q branch amp p v).1] using
    original_physical_pairing_finitePart q q branch amp p v

/-- The unchanged functional-equation reflected reader also leaves zero combined pairing finite part. -/
theorem reflected_physical_pairing_finitePart (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p v : Ici (0:ℝ)) :
    Tendsto (fun k : ℝ =>
      ((∫ w in SelbergModularDomainSlices.domain (Real.exp k),
        coexactPair (D4BMOriginalAngularGreen.source q branch amp p v)
          (physicalAngularParameter (xiZeroCopyReflectEquiv q)) ![w.1,w.2])+
        ((physicalAngularParameter (xiZeroCopyReflectEquiv q))^2-1/4)*
          (∫ w in SelbergModularDomainSlices.domain (Real.exp k),
            scalarDensity (D4BMOriginalAngularGreen.source q branch amp p v)
              (physicalAngularParameter (xiZeroCopyReflectEquiv q)) ![w.1,w.2]))-
        D4BMOriginalCuspFlux.pairingNonconstantFlux q (xiZeroCopyReflectEquiv q) branch amp p v k)
      atTop (𝓝 0) := by
  simpa only [(D4BMOriginalCuspFlux.pairingFluxConstant_original_readers q branch amp p v).2] using
    original_physical_pairing_finitePart q (xiZeroCopyReflectEquiv q) branch amp p v

end RHTower.D4BMOriginalScalarPairing
