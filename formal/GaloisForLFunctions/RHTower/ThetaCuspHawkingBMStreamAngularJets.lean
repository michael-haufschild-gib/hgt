import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSquareSourceCovector
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMScalarLinearEinsteinEquation

/-! Complete angular jets of the actual forced stream covectors. -/

open Set Filter Topology
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
open scoped ContDiff
namespace RHTower.D4BMModularCore
open D4BMHorizon D4BMMetricReconstruction D4BMVectorStream D4BMGlobalAngularResponse
noncomputable section

private theorem flat_div (V : Covector) (hD : ∀ z, 0 < z 1 → divergence V z = 0)
    (z : Point) (hz : 0 < z 1) : coordDeriv 0 (V 0) z+coordDeriv 1 (V 1) z = 0 := by
  have h := hD z hz
  rw [divergence_eq V z hz] at h
  exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr hz.ne'))

private theorem flat_div_partial (V : Covector) (hD : ∀ z, 0 < z 1 → divergence V z = 0)
    (z : Point) (hz : 0 < z 1) (hV : ∀ j, ContDiffAt ℝ 2 (V j) z) (k : Fin 2) :
    coordDeriv k (coordDeriv 0 (V 0)) z+coordDeriv k (coordDeriv 1 (V 1)) z = 0 := by
  have he : (fun w => coordDeriv 0 (V 0) w+coordDeriv 1 (V 1) w) =ᶠ[𝓝 z] (fun _ => (0:ℂ)) := by
    filter_upwards [(isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hz] with w hw
    exact flat_div V hD w hw
  have h0 := (coordDeriv_hasFDerivAt (hV 0) 0).differentiableAt
  have h1 := (coordDeriv_hasFDerivAt (hV 1) 1).differentiableAt
  have hd := congrArg (fun a => a (Pi.single k 1)) (he.fderiv_eq (𝕜 := ℝ))
  simpa [fderiv_fun_add h0 h1,coordDeriv] using hd

/-- The stream's angular jet, with every slot read from the actual covector. -/
def streamAngularJet (V : Covector) (k : Fin 2) (z : Point) : ScalarTwoJet (Fin 4) ℂ :=
  if k = 0 then covector0 (V 0 z) (coordDeriv 0 (V 0) z) (coordDeriv 1 (V 0) z)
    (coordDeriv 0 (coordDeriv 0 (V 0)) z) (coordDeriv 0 (coordDeriv 1 (V 0)) z)
    (coordDeriv 1 (coordDeriv 1 (V 0)) z)
  else covector1 (V 1 z) (coordDeriv 0 (V 0) z) (coordDeriv 0 (V 1) z)
    (coordDeriv 0 (coordDeriv 0 (V 0)) z) (coordDeriv 0 (coordDeriv 1 (V 0)) z)
    (coordDeriv 0 (coordDeriv 0 (V 1)) z)

/-- Both prescribed divergence-free stream jets are the complete actual pullback jets. -/
theorem streamAngularJet_actual (V : Covector) (p : D4BMBackground.ExteriorPoint)
    (hV : ∀ j, ContDiffAt ℝ 2 (V j) (angularPoint p.val))
    (hD : ∀ z, 0 < z 1 → divergence V z = 0) (k : Fin 2) :
    ofField (fun x => V k (angularPoint x)) p.val = streamAngularJet V k (angularPoint p.val) := by
  let z := angularPoint p.val
  have hz : 0 < z 1 := p.property.2
  have hc (j : Fin 2) : coordDeriv 1 (coordDeriv 0 (V j)) z =
      coordDeriv 0 (coordDeriv 1 (V j)) z := coordDeriv_commute (hV j) 1 0
  have hd : coordDeriv 1 (V 1) z = -coordDeriv 0 (V 0) z := by
    linear_combination flat_div V hD z hz
  have hxy : coordDeriv 0 (coordDeriv 1 (V 1)) z = -coordDeriv 0 (coordDeriv 0 (V 0)) z := by
    linear_combination flat_div_partial V hD z hz hV 0
  have hyy : coordDeriv 1 (coordDeriv 1 (V 1)) z = -coordDeriv 0 (coordDeriv 1 (V 0)) z := by
    have h := flat_div_partial V hD z hz hV 1
    rw [hc 0] at h
    linear_combination h
  rw [D4BMScalarLinearEquation.angular_lift_jet _ p.val (hV k)]
  fin_cases k <;> simp [streamAngularJet,covector0,covector1,← show z = angularPoint p.val from rfl,
    hc,hd,hxy,hyy]

/-- The angular slot used by the full Einstein stream contraction. -/
def streamAngularOperator (V : Covector) (k : Fin 2) (z : Point) : ℂ :=
  if k = 0 then (z 1 : ℂ)^2*(coordDeriv 0 (coordDeriv 0 (V 0)) z+
    coordDeriv 1 (coordDeriv 1 (V 0)) z)+2*(z 1 : ℂ)*(coordDeriv 1 (V 0) z-coordDeriv 0 (V 1) z)
  else (z 1 : ℂ)^2*(coordDeriv 0 (coordDeriv 0 (V 1)) z-coordDeriv 0 (coordDeriv 1 (V 0)) z)

/-- The stream angular slot equals the actual rough Laplacian plus its curvature correction. -/
theorem streamAngularOperator_actual (V : Covector) (z : Point) (hz : 0 < z 1)
    (hV : ∀ j, ContDiffAt ℝ 2 (V j) z) (hD : ∀ w, 0 < w 1 → divergence V w = 0) (k : Fin 2) :
    streamAngularOperator V k z = roughLaplacian V k z+V k z := by
  have hd := flat_div V hD z hz
  have hyy := flat_div_partial V hD z hz hV 1
  rw [coordDeriv_commute (hV 0) 1 0] at hyy
  rw [roughLaplacian_eq V z hz hV k]
  fin_cases k <;> simp [streamAngularOperator,roughFormula]
  linear_combination -(z 1 : ℂ)^2*hyy-2*(z 1 : ℂ)*hd

/-- The actual full-response angular stream slot contains the complete forcing J. -/
theorem streamAngularOperator_response (q : XiZeroCopy) (branch : Bool)
    (z : Point) (hz : 0 < z 1) (k : Fin 2) :
    streamAngularOperator (fullAngularCovector q branch) k z =
      parameter q branch*fullAngularCovector q branch k z+parameter q branch*fullSquareCovector q k z := by
  rw [streamAngularOperator_actual _ z hz _ (fullAngularCovector_divergence q branch),
    fullAngularCovector_rough_equation q branch z hz k]
  intro j
  have h := (contDiffAt_infty.mp (fullAngularCovector_smooth q branch z hz j)) 2
  norm_num at h
  exact h

/-- The actual quadratic-source angular stream slot retains both J and gradient-source K. -/
theorem streamAngularOperator_square (q : XiZeroCopy) (branch : Bool)
    (z : Point) (hz : 0 < z 1) (k : Fin 2) :
    streamAngularOperator (fullSquareCovector q) k z =
      2*(physicalRate q branch+1)*(physicalRate q branch+2)*fullSquareCovector q k z+
        2*fullGradientCovector q branch k z := by
  rw [streamAngularOperator_actual _ z hz _ (fullSquareCovector_divergence q),
    fullSquareCovector_rough_equation q branch z hz k]
  intro j
  simpa using fullSquareCovector_smooth q z hz 2 j

end
end RHTower.D4BMModularCore
