import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMMixedCurrentField
import GaloisForLFunctions.HTGeometry.SmoothTransitionDerivBound
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMForcedMetricTensor

/-! A fixed smooth ingoing onset for the original current. The tensor source
includes both derivatives of that onset. This constructs a current-sector
source extension, not the nonlinear causal solution or its extinction law. -/

open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
open Set Filter Topology
namespace RHTower.D4BMModularCore
open D4BMHorizon D4BMIngoingCoordinates D4BMQuadraticMixedSource D4BMFundamentalScalarMetric D4BMMetricReconstruction
set_option autoImplicit false
noncomputable section

/-- Original ingoing time in the static exterior chart. -/
def ingoingTime (x : Fin 4 → ℝ) : ℝ := x 0+tortoise (x 1)

/-- One fixed smooth onset, independent of the Xi occurrence and source amplitude. -/
def currentCutoff (x : Fin 4 → ℝ) : ℂ := ((Real.smoothTransition (ingoingTime x) : ℝ) : ℂ)

/-- The actual derivative of the fixed onset profile at ingoing time. -/
def currentCutoffSlope (x : Fin 4 → ℝ) : ℂ := ((deriv Real.smoothTransition (ingoingTime x) : ℝ) : ℂ)

private def timeDifferential (r : ℝ) : (Fin 4 → ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.proj 0+(r^(2 : ℕ)-1)⁻¹ • ContinuousLinearMap.proj 1

private theorem time_derivative (p : D4BMBackground.ExteriorPoint) :
    HasFDerivAt ingoingTime (timeDifferential (p.val 1)) p.val := by
  have h := HasDerivAt.comp_hasFDerivAt (𝕜 := ℝ) (𝕜' := ℝ)
    (f := fun x : Fin 4 → ℝ => x 1) p.val
    (tortoise_hasDerivAt (p.val 1) p.property.1) (hasFDerivAt_apply 1 p.val)
  exact (hasFDerivAt_apply 0 p.val).add h

private theorem cutoff_derivative (p : D4BMBackground.ExteriorPoint) :
    HasFDerivAt currentCutoff
      (Complex.ofRealCLM.comp ((ContinuousLinearMap.toSpanSingleton ℝ (deriv Real.smoothTransition (ingoingTime p.val))).comp (timeDifferential (p.val 1)))) p.val := by
  have hχ := ((Real.smoothTransition.contDiff (n := 1)).differentiable (by norm_num)).differentiableAt.hasDerivAt
    (x := ingoingTime p.val)
  exact Complex.ofRealCLM.hasFDerivAt.comp p.val (hχ.hasFDerivAt.comp p.val (time_derivative p))

/-- The actual onset gradient has both time and radial components, with the
radial factor fixed by the original tortoise coordinate derivative. -/
theorem currentCutoff_derivatives (p : D4BMBackground.ExteriorPoint) :
    coordDeriv 0 currentCutoff p.val = currentCutoffSlope p.val ∧
    coordDeriv 1 currentCutoff p.val = currentCutoffSlope p.val/((p.val 1 : ℂ)^(2 : ℕ)-1) := by
  have h := (cutoff_derivative p).fderiv
  constructor <;> simp [coordDeriv,h,timeDifferential,currentCutoffSlope,div_eq_mul_inv,mul_comm]

/-- The original current multiplied by the fixed ingoing onset. -/
def switchedOrbitCurrent (q : XiZeroCopy) (branch : Bool) (a : ℂ) (z : Point) (k : Fin 2)
    (x : Fin 4 → ℝ) : ℂ := currentCutoff x*orbitCurrent q branch a z k x

/-- Both source-producing derivatives retain the exact cutoff derivative terms. -/
theorem switchedOrbitCurrent_derivatives (q : XiZeroCopy) (branch : Bool) (a : ℂ) (z : Point) (k : Fin 2)
    (p : D4BMBackground.ExteriorPoint) :
    coordDeriv 0 (switchedOrbitCurrent q branch a z k) p.val =
      currentCutoff p.val*(currentRate q branch*orbitCurrent q branch a z k p.val)+
        currentCutoffSlope p.val*orbitCurrent q branch a z k p.val ∧
    coordDeriv 1 (switchedOrbitCurrent q branch a z k) p.val =
      currentCutoff p.val*currentFirst (physicalRate q branch) (p.val 1)
        (envelope (physicalRate q branch) a p.val) (fullSquareCovector q k z) (fullGradientCovector q branch k z)+
      currentCutoffSlope p.val/((p.val 1:ℂ)^(2 : ℕ)-1)*orbitCurrent q branch a z k p.val := by
  have hc := (cutoff_derivative p).differentiableAt
  have hC := (orbitCurrent_smooth q branch a z k p).differentiableAt (by norm_num)
  have h0 := (orbitCurrent_derivatives q branch a z k p).1
  have h1 := (orbitCurrent_derivatives q branch a z k p).2
  unfold switchedOrbitCurrent
  constructor
  · rw [coordDeriv_mul hc hC,(currentCutoff_derivatives p).1,h0]
    ring
  · rw [coordDeriv_mul hc hC,(currentCutoff_derivatives p).2,h1]
    ring

/-- The complete tensor source obtained by differentiating the switched current,
with both angular components and their symmetric partners. -/
def switchedCurrentSource (q : XiZeroCopy) (branch : Bool) (a : ℂ) (x : Fin 4 → ℝ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  let r := (x 1 : ℂ)
  let C := switchedOrbitCurrent q branch a (angularPoint x)
  let T := fun k => (r^(2 : ℕ)-1)/r^(2 : ℕ)*coordDeriv 1 (C k) x
  let R := fun k => 1/(r^(2 : ℕ)*(r^(2 : ℕ)-1))*coordDeriv 0 (C k) x
  !![0,0,T 0,T 1; 0,0,R 0,R 1; T 0,R 0,0,0; T 1,R 1,0,0]

/-- The explicit onset tensor required in addition to a cutoff times the
original source. Its two blocks differ by the original radial factor. -/
def currentOnsetTensor (q : XiZeroCopy) (branch : Bool) (a : ℂ) (x : Fin 4 → ℝ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  let r := (x 1 : ℂ)
  let D := fun k => currentCutoffSlope x*orbitCurrent q branch a (angularPoint x) k x
  let T := fun k => D k/r^(2 : ℕ)
  let R := fun k => D k/(r^(2 : ℕ)*(r^(2 : ℕ)-1))
  !![0,0,T 0,T 1; 0,0,R 0,R 1; T 0,R 0,0,0; T 1,R 1,0,0]

/-- Exact original-source plus onset decomposition in every tensor component.
Switching the current cannot discard its differentiated onset tensor. -/
theorem switchedCurrentSource_eq (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (p : D4BMBackground.ExteriorPoint) (i j : Fin 4) :
    switchedCurrentSource q branch a p.val i j =
      currentCutoff p.val*literalMixedSource q branch (p.val 1)
        (envelope (physicalRate q branch) a p.val) (angularPoint p.val) i j+
      currentOnsetTensor q branch a p.val i j := by
  let s := physicalRate q branch
  let r := (p.val 1 : ℂ)
  let B := envelope s a p.val
  let z := angularPoint p.val
  have hr : r ≠ 0 := by dsimp only [r]; exact_mod_cast (by linarith [p.property.1] : p.val 1 ≠ 0)
  have hf : r^(2 : ℕ)-1 ≠ 0 := by dsimp only [r]; exact_mod_cast (by nlinarith [p.property.1] : (p.val 1)^(2 : ℕ)-1 ≠ 0)
  have ht (k : Fin 2) :
      (r^(2 : ℕ)-1)/r^(2 : ℕ)*coordDeriv 1 (switchedOrbitCurrent q branch a z k) p.val =
      currentCutoff p.val*(B^(2 : ℕ)*(timeSquare s r*fullSquareCovector q k z+timeGradient s r*fullGradientCovector q branch k z))+
      currentCutoffSlope p.val*orbitCurrent q branch a z k p.val/r^(2 : ℕ) := by
    rw [(switchedOrbitCurrent_derivatives q branch a z k p).2]
    rw [← temporal_current s r B (fullSquareCovector q k z) (fullGradientCovector q branch k z) hr hf]
    dsimp only [s,r,B,z] at hr hf ⊢
    field_simp [hr,hf]
  have hv (k : Fin 2) :
      1/(r^(2 : ℕ)*(r^(2 : ℕ)-1))*coordDeriv 0 (switchedOrbitCurrent q branch a z k) p.val =
      currentCutoff p.val*(B^(2 : ℕ)*(radialSquare s r*fullSquareCovector q k z+radialGradient s r*fullGradientCovector q branch k z))+
      currentCutoffSlope p.val*orbitCurrent q branch a z k p.val/(r^(2 : ℕ)*(r^(2 : ℕ)-1)) := by
    rw [(switchedOrbitCurrent_derivatives q branch a z k p).1]
    have h := radial_current s r B (fullSquareCovector q k z) (fullGradientCovector q branch k z) hr hf
    change r^(2 : ℕ)*(r^(2 : ℕ)-1)*(B^(2 : ℕ)*(radialSquare s r*fullSquareCovector q k z+radialGradient s r*fullGradientCovector q branch k z)) =
      currentRate q branch*orbitCurrent q branch a z k p.val at h
    rw [← h]
    field_simp [hr,hf]
  fin_cases i <;> fin_cases j
  all_goals first | exact ht 0 | exact ht 1 | exact hv 0 | exact hv 1 |
    simp [switchedCurrentSource,currentOnsetTensor,literalMixedSource]

/-- Before ingoing onset, the entire switched source tensor vanishes. -/
theorem switchedCurrentSource_zero_before (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (p : D4BMBackground.ExteriorPoint) (hp : ingoingTime p.val < 0) (i j : Fin 4) :
    switchedCurrentSource q branch a p.val i j = 0 := by
  rw [switchedCurrentSource_eq]
  have hc := Real.smoothTransition.zero_of_nonpos hp.le
  have hd := deriv_smoothTransition_eq_zero_of_notMem (show ingoingTime p.val ∉ Icc (0:ℝ) 1 by intro h; exact (not_le_of_gt hp) h.1)
  fin_cases i <;> fin_cases j <;> simp [currentCutoff,hc,currentOnsetTensor,currentCutoffSlope,hd]

/-- After the fixed onset interval, the tensor is exactly the original literal
mixed source at every exterior point; no angular or radial term is replaced. -/
theorem switchedCurrentSource_eq_after (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (p : D4BMBackground.ExteriorPoint) (hp : 1 < ingoingTime p.val) (i j : Fin 4) :
    switchedCurrentSource q branch a p.val i j =
      literalMixedSource q branch (p.val 1) (envelope (physicalRate q branch) a p.val)
        (angularPoint p.val) i j := by
  rw [switchedCurrentSource_eq]
  have hc := Real.smoothTransition.one_of_one_le hp.le
  have hd := deriv_smoothTransition_eq_zero_of_notMem (show ingoingTime p.val ∉ Icc (0:ℝ) 1 by intro h; exact (not_le_of_gt hp) h.2)
  fin_cases i <;> fin_cases j <;> simp [currentCutoff,hc,currentOnsetTensor,currentCutoffSlope,hd]

end
end RHTower.D4BMModularCore
