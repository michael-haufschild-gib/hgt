import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalOrbitCusp
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalModularOrbit
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalCuspFlux

/-!
The first original metric cusp flux retains the differentiated causal source and
full normalizable reader. Both reader normal derivatives and the complete
forcing decomposition are derived for the second metric term. Its source-contact
cusp remainder and the temporal/horizon comparison remain to be attached.
All cusp bounds here keep time and exterior radius fixed.
-/
open Set Filter Topology MeasureTheory
open scoped ContDiff
open GaloisForLFunctions.HTGeometry ScalarTwoJet
namespace RHTower.D4BMOriginalMetricCusp
open D4BMJointSource D4BMOriginalAngularCurrent D4BMOriginalOrbitCurrent
open D4BMOriginalSourceContact D4BMOriginalReaderEquation D4BMOriginalOrbitCusp
open D4BMOriginalCuspFlux D4BMMetricReconstruction
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal
attribute [-instance] RCLike.innerProductSpace
private abbrev P := Fin 4 → ℝ
private abbrev A := Fin 2 → ℝ

private theorem coordinate_update {n : ℕ} (f : (Fin n → ℝ) → ℂ)
    (x : Fin n → ℝ) (i : Fin n) (hf : DifferentiableAt ℝ f x) :
    coordDeriv i f x=deriv (fun a => f (Function.update x i a)) (x i) := by
  have hf' : HasFDerivAt f (fderiv ℝ f x) (Function.update x i (x i)) := by
    simpa only [Function.update_eq_self] using hf.hasFDerivAt
  have h := hf'.comp_hasDerivAt (x i) (hasDerivAt_update x i (x i))
  simpa only [Function.update_eq_self,coordDeriv,Function.comp_def] using h.deriv.symm

private theorem scalar_normal (r : XiZeroCopy) (z : A) (hy : 0<z 1) :
    coordDeriv 1 (D4BMLiteralCusp.scalar (physicalAngularParameter r)) z=
      deriv (fun Y => D4BMLiteralCusp.scalar (physicalAngularParameter r) ![z 0,Y]) (z 1) := by
  rw [coordinate_update _ _ _ ((D4BMLiteralCusp.scalar_contDiffAt
    (physicalAngularParameter r) 2 z hy).differentiableAt (by norm_num))]
  congr 1

/-- Genuine normal differentiation of the unchanged physical left scalar. -/
theorem reader_normal (r : XiZeroCopy) (side outer : Bool) (x : P)
    (hr : 1<x 1) (hy : 0<x 3) :
    coordDeriv 3 (leftScalar r side outer) x=
      leftAmplitude r side outer ![x 0,x 1]*
        coordDeriv 1 (D4BMLiteralCusp.scalar (physicalAngularParameter r)) ![x 2,x 3] := by
  rw [coordinate_update _ _ _ ((leftScalar_smooth r side outer x hr hy).differentiableAt (by simp))]
  simp_rw [leftScalar_value]
  simp only [angularPoint,Function.update_self,
    Function.update_of_ne (by decide : (0:Fin 4)≠3),
    Function.update_of_ne (by decide : (1:Fin 4)≠3),
    Function.update_of_ne (by decide : (2:Fin 4)≠3)]
  rw [deriv_const_mul_field,scalar_normal r ![x 2,x 3] hy]
  rfl

/-- The reader contact is differentiated as the actual exterior germ. -/
theorem reader_contact_normal (r : XiZeroCopy) (side outer : Bool) (x : P)
    (hr : 1<x 1) (hy : 0<x 3) :
    coordDeriv 3 (scalarContact (leftScalar r side outer)) x=
      (D4BMLeftModeRadialEquation.eigenvalue r-2)*leftAmplitude r side outer ![x 0,x 1]*
        coordDeriv 1 (D4BMLiteralCusp.scalar (physicalAngularParameter r)) ![x 2,x 3] := by
  have he : scalarContact (leftScalar r side outer)=ᶠ[𝓝 x]
      fun z => (D4BMLeftModeRadialEquation.eigenvalue r-2)*leftScalar r side outer z := by
    filter_upwards [(isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hr,
      (isOpen_lt continuous_const (continuous_apply 3)).mem_nhds hy] with z hR hY
    exact left_scalar_contact r side outer z hR hY
  have hf := (leftScalar_smooth r side outer x hr hy).differentiableAt (by simp)
  change fderiv ℝ (scalarContact (leftScalar r side outer)) x (Pi.single 3 1)=_
  rw [he.fderiv_eq,fderiv_const_mul hf]
  change (D4BMLeftModeRadialEquation.eigenvalue r-2)*coordDeriv 3 (leftScalar r side outer) x=_
  rw [reader_normal r side outer x hr hy]
  ring


/-- Actual ingoing orbit coefficient of the original left reader. -/
def readerOrbitAmplitude (r : XiZeroCopy) (side outer : Bool) (j : Fin 2) (p R : ℝ) : ℂ :=
  if j=0 then deriv (fun u => leftAmplitude r side outer ![p,u]) R
  else ((R:ℂ)^2-1)*deriv (fun u => leftAmplitude r side outer ![p,u]) R+
    deriv (fun u => leftAmplitude r side outer ![u,R]) p

/-- Original reader orbit differentiation retains its literal angular field. -/
theorem reader_orbit_value (r : XiZeroCopy) (side outer : Bool) (j : Fin 2) (x : P)
    (hr : 1<x 1) (hy : 0<x 3) :
    orbitDerivative (leftScalar r side outer) j x=
      readerOrbitAmplitude r side outer j (x 0) (x 1)*
        D4BMLiteralCusp.scalar (physicalAngularParameter r) ![x 2,x 3] := by
  have hf := (leftScalar_smooth r side outer x hr hy).differentiableAt (by simp)
  have hR : coordDeriv 1 (leftScalar r side outer) x=
      deriv (fun u => leftAmplitude r side outer ![x 0,u]) (x 1)*
        D4BMLiteralCusp.scalar (physicalAngularParameter r) ![x 2,x 3] := by
    rw [coordinate_update _ _ _ hf]
    simp_rw [leftScalar_value]
    simp only [angularPoint,Function.update_self,
      Function.update_of_ne (by decide : (0:Fin 4)≠1),
      Function.update_of_ne (by decide : (2:Fin 4)≠1),
      Function.update_of_ne (by decide : (3:Fin 4)≠1)]
    rw [deriv_mul_const_field]
    rfl
  have hp : coordDeriv 0 (leftScalar r side outer) x=
      deriv (fun u => leftAmplitude r side outer ![u,x 1]) (x 0)*
        D4BMLiteralCusp.scalar (physicalAngularParameter r) ![x 2,x 3] := by
    rw [coordinate_update _ _ _ hf]
    simp_rw [leftScalar_value]
    simp only [angularPoint,Function.update_self,
      Function.update_of_ne (by decide : (1:Fin 4)≠0),
      Function.update_of_ne (by decide : (2:Fin 4)≠0),
      Function.update_of_ne (by decide : (3:Fin 4)≠0)]
    rw [deriv_mul_const_field]
    rfl
  by_cases hj : j=0
  · simpa only [orbitDerivative,readerOrbitAmplitude,if_pos hj] using hR
  · simp only [orbitDerivative,readerOrbitAmplitude,if_neg hj,hR,hp]
    ring

private theorem reader_orbit_differentiable (r : XiZeroCopy) (side outer : Bool)
    (j : Fin 2) (x : P) (hr : 1<x 1) (hy : 0<x 3) :
    DifferentiableAt ℝ (orbitDerivative (leftScalar r side outer) j) x := by
  have hW := leftScalar_smooth r side outer x hr hy
  have hCR : ContDiffAt ℝ ∞ (coordDeriv 1 (leftScalar r side outer)) x :=
    coordDeriv_contDiffAt hW (by simp) 1
  have hCp : ContDiffAt ℝ ∞ (coordDeriv 0 (leftScalar r side outer)) x :=
    coordDeriv_contDiffAt hW (by simp) 0
  have hR := hCR.differentiableAt (by simp)
  have hp := hCp.differentiableAt (by simp)
  have hrad : DifferentiableAt ℝ (fun z : P => (z 1:ℂ)^2-1) x := by fun_prop
  change DifferentiableAt ℝ (fun z => if j=0 then coordDeriv 1 (leftScalar r side outer) z
    else ((z 1:ℂ)^2-1)*coordDeriv 1 (leftScalar r side outer) z+
      coordDeriv 0 (leftScalar r side outer) z) x
  by_cases hj : j=0
  · simpa only [if_pos hj] using hR
  · simp only [if_neg hj]
    exact (hrad.mul hR).add hp

/-- The second metric transfer's reader normal derivative keeps the actual time/radius coefficient. -/
theorem reader_orbit_normal (r : XiZeroCopy) (side outer : Bool) (j : Fin 2) (x : P)
    (hr : 1<x 1) (hy : 0<x 3) :
    coordDeriv 3 (orbitDerivative (leftScalar r side outer) j) x=
      readerOrbitAmplitude r side outer j (x 0) (x 1)*
        coordDeriv 1 (D4BMLiteralCusp.scalar (physicalAngularParameter r)) ![x 2,x 3] := by
  let G : P → ℂ := fun z => readerOrbitAmplitude r side outer j (z 0) (z 1)*
    D4BMLiteralCusp.scalar (physicalAngularParameter r) ![z 2,z 3]
  have he : orbitDerivative (leftScalar r side outer) j=ᶠ[𝓝 x] G := by
    filter_upwards [(isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hr,
      (isOpen_lt continuous_const (continuous_apply 3)).mem_nhds hy] with z hR hY
    exact reader_orbit_value r side outer j z hR hY
  have hG := (reader_orbit_differentiable r side outer j x hr hy).congr_of_eventuallyEq he.symm
  change fderiv ℝ (orbitDerivative (leftScalar r side outer) j) x (Pi.single 3 1)=_
  rw [he.fderiv_eq]
  change coordDeriv 3 G x=_
  rw [coordinate_update _ _ _ hG]
  simp only [G,Function.update_self,
    Function.update_of_ne (by decide : (0:Fin 4)≠3),
    Function.update_of_ne (by decide : (1:Fin 4)≠3),
    Function.update_of_ne (by decide : (2:Fin 4)≠3)]
  rw [deriv_const_mul_field,scalar_normal r ![x 2,x 3] hy]
  rfl

/-- Original source scale, including the complete fixed onset. -/
def forcingScale (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (p R : ℝ) : ℂ :=
  let s := D4BMModularCore.physicalRate q branch
  let t := D4BMIngoingCoordinates.tortoise R
  let u := (radialUnit t:ℂ);
  -2*(1-u^2)*u*sourceAmplitude s 0 amp 1 t*timeOnset (2*s) p

def forcingValueCoefficient (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (p R : ℝ) : ℂ :=
  let s := D4BMModularCore.physicalRate q branch
  let u := (radialUnit (D4BMIngoingCoordinates.tortoise R):ℂ)
  forcingScale q branch amp p R*((5*s^2+15*s+4)/4+s*(s-1)*u^2*(s+2)*(2*s+3)/4)

def forcingLaplacianCoefficient (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (p R : ℝ) : ℂ :=
  let s := D4BMModularCore.physicalRate q branch
  let u := (radialUnit (D4BMIngoingCoordinates.tortoise R):ℂ)
  forcingScale q branch amp p R*(-s*(s-1)*u^2/8)

/-- Full gradient energy is retained through the actual angular equation, not discarded. -/
theorem original_forcing_laplacian (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (x : P) (hy : 0<x 3) :
    D4BMOriginalSourceContact.originalForcing q branch amp x=
      forcingValueCoefficient q branch amp (x 0) (x 1)*D4BMModularCore.fullSquarePotential q ![x 2,x 3]+
      forcingLaplacianCoefficient q branch amp (x 0) (x 1)*
        D4BMHorizon.scalarLaplacian (D4BMModularCore.fullSquarePotential q) ![x 2,x 3] := by
  rw [D4BMModularCore.fullSquarePotential_laplacian q branch ![x 2,x 3] hy]
  simp only [D4BMOriginalSourceContact.originalForcing,timeOriginalForcing,
    D4BMJointSource.originalForcing,sub_add_cancel]
  dsimp only [forcingValueCoefficient,forcingLaplacianCoefficient,forcingScale]
  ring

/-- Source-derived principal coefficient of the first original metric top flux. -/
def firstFluxCoefficient (q r : XiZeroCopy) (branch side outer : Bool) (amp : ℂ)
    (j : Fin 2) (p R : ℝ) (i : Fin 3) : ℂ :=
  (D4BMLeftModeRadialEquation.eigenvalue r-2)*leftAmplitude r side outer ![p,R]*
    (principalOrbitCoefficient q branch amp j p R i*readerCoefficient r*readerExponent r)

/-- The first complete metric transfer uses the genuine orbit source and reader-contact normal derivative. -/
theorem first_metric_cusp_expansion (q r : XiZeroCopy) (branch side outer : Bool) (amp : ℂ)
    (p R : ℝ) (hp : 0<p) (hr : 1<R) (j : Fin 2) (w : ℂ) :
    Tendsto (fun k : ℝ => ∫ X in (-1/2:ℝ)..1/2, Complex.exp (w*(k:ℂ))*
      (transfer (orbitDerivative (sourceScalar q branch amp) j)
        (scalarContact (leftScalar r side outer)) 1 ![p,R,X,Real.exp k]-
      ∑ i : Fin 3, firstFluxCoefficient q r branch side outer amp j p R i*
        Complex.exp (fluxExponent q r i*(k:ℂ)))) atTop (𝓝 0) := by
  let b := (D4BMLeftModeRadialEquation.eigenvalue r-2)*leftAmplitude r side outer ![p,R]
  have ht := normal_flux_integral_of_expansion q r
    (fun z : A => orbitDerivative (sourceScalar q branch amp) j ![p,R,z 0,z 1])
    (principalOrbitCoefficient q branch amp j p R)
    (fun X w => original_orbit_expansion q branch amp p R hp hr X w j) w
  have h := ht.const_mul b
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [] with k
  have hs : (∑ i : Fin 3, firstFluxCoefficient q r branch side outer amp j p R i*
      Complex.exp (fluxExponent q r i*(k:ℂ)))=
      b*∑ i : Fin 3, principalOrbitCoefficient q branch amp j p R i*readerCoefficient r*
        readerExponent r*Complex.exp (fluxExponent q r i*(k:ℂ)) := by
    simp only [firstFluxCoefficient,b,Finset.mul_sum,mul_assoc]
  rw [hs]
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro X _
  change b*(Complex.exp (w*(k:ℂ))*
    (orbitDerivative (sourceScalar q branch amp) j ![p,R,X,Real.exp k]*
      coordDeriv 1 (D4BMLiteralCusp.scalar (physicalAngularParameter r)) ![X,Real.exp k]-_))=
    Complex.exp (w*(k:ℂ))*(orbitDerivative (sourceScalar q branch amp) j ![p,R,X,Real.exp k]*
      coordDeriv 3 (scalarContact (leftScalar r side outer)) ![p,R,X,Real.exp k]-_)
  rw [reader_contact_normal r side outer ![p,R,X,Real.exp k] hr (Real.exp_pos k)]
  simp only [Matrix.cons_val]
  dsimp only [b]
  ring

/-- No constant cusp term occurs in this actual metric transfer for either original reader. -/
theorem first_metric_cusp_constant (q r : XiZeroCopy) (branch side outer : Bool) (amp : ℂ)
    (p R : ℝ) (j : Fin 2)
    (h : (r.1:ℂ).im=(q.1:ℂ).im ∨ (r.1:ℂ).im= -(q.1:ℂ).im) :
    (∑ i : Fin 3, if fluxExponent q r i=0 then
      firstFluxCoefficient q r branch side outer amp j p R i else 0)=0 := by
  classical
  simp only [fluxExponent_nonzero_original q r h,if_false,Finset.sum_const_zero]

end
end RHTower.D4BMOriginalMetricCusp
