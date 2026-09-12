import GaloisForLFunctions.HTGeometry.ComplexMetricJetDerivative
import GaloisForLFunctions.HTGeometry.CoordinateEinsteinAffineSpatialVariation

set_option autoImplicit false
namespace GaloisForLFunctions.HTGeometry.ComplexMetricField
open ScalarTwoJet ComplexCoordinateMetricTwoJet Filter Topology
noncomputable section
variable {d : ℕ}
local notation "Space" => ComplexMetricTwoJetSpace d

/-- The original affine metric field, before any projection or source truncation. -/
def affineField (g h : Field d) (e : ℂ) : Field d := fun x => g x+e • h x

/-- The original Einstein Hessian on actual field jets. Its Taylor coefficient is one half. -/
def hessianField (g h : Field d) (x : Fin d → ℝ) (i j : Fin d) : ℂ :=
  secondVariation (jetSpace g x) i j (jetSpace h x) (jetSpace h x)

/-- The actual Hessian field is differentiable, rather than only linewise realizable. -/
theorem hessianField_differentiableAt (g h : Field d) (x : Fin d → ℝ)
    (hg : ∀ i j, ContDiffAt ℝ 3 (fun y => g y i j) x)
    (hh : ∀ i j, ContDiffAt ℝ 3 (fun y => h y i j) x)
    (hdet : (g x).det ≠ 0) (i j : Fin d) :
    DifferentiableAt ℝ (fun y => hessianField g h y i j) x := by
  have hA := contDiffAt_einsteinComponent (n := 3) (jetSpace g x) hdet i j
  have hH := (hA.fderiv_right (m := 2) (by norm_num)).fderiv_right (m := 1) (by norm_num)
  have hF : ContDiffAt ℂ 1 (fun z : Space × Space => z.1) (jetSpace g x,jetSpace h x) := contDiffAt_fst
  have hP : ContDiffAt ℂ 1 (fun z : Space × Space => z.2) (jetSpace g x,jetSpace h x) := contDiffAt_snd
  have hS := ((hH.comp (jetSpace g x,jetSpace h x) hF).clm_apply hP).clm_apply hP
  have hR := (hS.differentiableAt (by norm_num)).restrictScalars ℝ
  have hQ := (jetSpace_differentiableAt g x hg).prodMk (jetSpace_differentiableAt h x hh)
  convert! hR.comp x hQ using 1

/-- The actual spatial derivative of the full Einstein Hessian. -/
theorem hessianField_coordDeriv (g h : Field d) (x : Fin d → ℝ)
    (hg : ∀ i j, ContDiffAt ℝ 3 (fun y => g y i j) x)
    (hh : ∀ i j, ContDiffAt ℝ 3 (fun y => h y i j) x)
    (hdet : (g x).det ≠ 0) (k i j : Fin d) :
    coordDeriv k (fun y => hessianField g h y i j) x =
      thirdVariation (jetSpace g x) i j (jetSpace h x) (jetSpace h x) (jetSpacePartial g x k)+
        2*secondVariation (jetSpace g x) i j (jetSpace h x) (jetSpacePartial h x k) := by
  exact (field_coordinateLine_hasDerivAt (hessianField_differentiableAt g h x hg hh hdet i j) k).unique
    (hessian_coordinateLine_hasDerivAt g h x hg hh hdet k i j)

/-- Spatial differentiation of the original affine Einstein field is its full jet variation. -/
theorem affineEinstein_coordDeriv (g h : Field d) (x : Fin d → ℝ) (e : ℂ)
    (hg : ∀ i j, ContDiffAt ℝ 3 (fun y => g y i j) x)
    (hh : ∀ i j, ContDiffAt ℝ 3 (fun y => h y i j) x)
    (hdet : (affineField g h e x).det ≠ 0) (k i j : Fin d) :
    coordDeriv k (fun y => (twoJet (affineField g h e) y).einstein i j) x =
      affineSpatialEinstein (jetSpace g x) (jetSpace h x)
        (jetSpacePartial g x k) (jetSpacePartial h x k) i j e := by
  rw [einsteinField_coordDeriv (affineField g h e) x
    (fun i j => (hg i j).add (contDiffAt_const.mul (hh i j))) hdet]
  unfold affineField
  rw [jetSpace_add_smul g h x e (fun i j => (hg i j).of_le (by norm_num))
    (fun i j => (hh i j).of_le (by norm_num)),jetSpacePartial_add_smul g h x e hg hh]
  rfl

/-- Two amplitude derivatives commute with one actual spatial derivative of the original
Einstein field. All third derivatives and both mixed terms are produced, not assumed. -/
theorem einstein_mixed_derivatives (g h : Field d) (x : Fin d → ℝ)
    (hg : ∀ i j, ContDiffAt ℝ 3 (fun y => g y i j) x)
    (hh : ∀ i j, ContDiffAt ℝ 3 (fun y => h y i j) x)
    (hdet : (g x).det ≠ 0) (k i j : Fin d) :
    deriv (deriv (fun e => coordDeriv k
      (fun y => (twoJet (affineField g h e) y).einstein i j) x)) 0 =
        coordDeriv k (fun y => hessianField g h y i j) x := by
  have hc : Continuous (fun e => (affineField g h e x).det) := by
    simp only [Matrix.det_apply',affineField,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
    fun_prop
  have hd : (affineField g h 0 x).det ≠ 0 := by simpa [affineField] using hdet
  have he : (fun e => coordDeriv k (fun y => (twoJet (affineField g h e) y).einstein i j) x) =ᶠ[𝓝 0]
      affineSpatialEinstein (jetSpace g x) (jetSpace h x)
        (jetSpacePartial g x k) (jetSpacePartial h x k) i j := by
    filter_upwards [hc.continuousAt.eventually_ne hd] with e he
    exact affineEinstein_coordDeriv g h x e hg hh he k i j
  rw [he.deriv.deriv_eq,affineSpatialEinstein_second _ _ _ _ i j hdet,
    hessianField_coordDeriv g h x hg hh hdet]

end
end GaloisForLFunctions.HTGeometry.ComplexMetricField
