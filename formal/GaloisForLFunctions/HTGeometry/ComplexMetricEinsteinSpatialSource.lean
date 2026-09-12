import GaloisForLFunctions.HTGeometry.ComplexMetricEinsteinSourceVariation
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

set_option autoImplicit false
namespace GaloisForLFunctions.HTGeometry.ComplexMetricField
open ScalarTwoJet ComplexCoordinateMetricTwoJet Filter Topology
open scoped ContDiff
noncomputable section
variable {d : ℕ}

/-- Actual coordinate derivative of the full cosmological source. -/
def spatialSource (g h : Field d) (Λ : ℂ) (x : Fin d → ℝ) (k i j : Fin d) (e : ℂ) : ℂ :=
  coordDeriv k (fun y => affineSource g h Λ y i j e) x

/-- Full jet expression for the spatial source, including its affine cosmological part. -/
def spatialSourceModel (g h : Field d) (Λ : ℂ) (x : Fin d → ℝ) (k i j : Fin d) (e : ℂ) : ℂ :=
  affineSpatialEinstein (jetSpace g x) (jetSpace h x)
      (jetSpacePartial g x k) (jetSpacePartial h x k) i j e+
    Λ*(coordDeriv k (fun y => g y i j) x+e*coordDeriv k (fun y => h y i j) x)

theorem spatialSource_eq (g h : Field d) (Λ : ℂ) (x : Fin d → ℝ)
    (hg : ∀ i j, ContDiffAt ℝ 3 (fun y => g y i j) x)
    (hh : ∀ i j, ContDiffAt ℝ 3 (fun y => h y i j) x)
    (e : ℂ) (hdet : (affineField g h e x).det ≠ 0) (k i j : Fin d) :
    spatialSource g h Λ x k i j e = spatialSourceModel g h Λ x k i j e := by
  have ha (a b : Fin d) : ContDiffAt ℝ 3 (fun y => affineField g h e y a b) x :=
    (hg a b).add (contDiffAt_const.mul (hh a b))
  have hE := einsteinField_differentiableAt (affineField g h e) x ha hdet i j
  have hG := (hg i j).differentiableAt (by norm_num)
  have hH := (hh i j).differentiableAt (by norm_num)
  change coordDeriv k (fun y => (twoJet (affineField g h e) y).einstein i j+
    Λ*(g y i j+e*h y i j)) x = _
  rw [coordDeriv_add (f := fun y => (twoJet (affineField g h e) y).einstein i j)
    (g := fun y => Λ*(g y i j+e*h y i j)) hE ((differentiableAt_const Λ).mul
    (hG.add ((differentiableAt_const e).mul hH))),
    affineEinstein_coordDeriv g h x e hg hh hdet]
  rw [coordDeriv_mul (f := fun _ => Λ) (g := fun y => g y i j+e*h y i j) (differentiableAt_const Λ)
      (hG.add ((differentiableAt_const e).mul hH)),
    coordDeriv_add (f := fun y => g y i j) (g := fun y => e*h y i j) hG ((differentiableAt_const e).mul hH),
    coordDeriv_mul (f := fun _ => e) (g := fun y => h y i j) (differentiableAt_const e) hH]
  simp [spatialSourceModel,coordDeriv]

theorem spatialSource_eventuallyEq (g h : Field d) (Λ : ℂ) (x : Fin d → ℝ)
    (hg : ∀ i j, ContDiffAt ℝ 3 (fun y => g y i j) x)
    (hh : ∀ i j, ContDiffAt ℝ 3 (fun y => h y i j) x)
    (hdet : (g x).det ≠ 0) (k i j : Fin d) :
    spatialSource g h Λ x k i j =ᶠ[𝓝 0] spatialSourceModel g h Λ x k i j := by
  have hc : Continuous (fun e => (affineField g h e x).det) := by
    simp only [Matrix.det_apply',affineField,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]; fun_prop
  have hd : (affineField g h 0 x).det ≠ 0 := by simpa [affineField] using hdet
  filter_upwards [hc.continuousAt.eventually_ne hd] with e he
  exact spatialSource_eq g h Λ x hg hh e he k i j

theorem spatialSourceModel_contDiffAt (g h : Field d) (Λ : ℂ) (x : Fin d → ℝ)
    (hdet : (g x).det ≠ 0) (k i j : Fin d) :
    ContDiffAt ℂ 2 (spatialSourceModel g h Λ x k i j) 0 := by
  have hd : Matrix.det (amplitudeJet (jetSpace g x) (jetSpace h x) 0).1 ≠ 0 := by
    simpa [amplitudeJet,jetSpace,toSpace,twoJet] using hdet
  have hA := (contDiffAt_einsteinComponent (n := 3) _ hd i j).fderiv_right (m := 2) (by norm_num)
  have hQ : ContDiffAt ℂ 2 (amplitudeJet (jetSpace g x) (jetSpace h x)) 0 := by
    unfold amplitudeJet; fun_prop
  have hP : ContDiffAt ℂ 2 (amplitudeJet (jetSpacePartial g x k) (jetSpacePartial h x k)) 0 := by
    unfold amplitudeJet; fun_prop
  exact ((hA.comp 0 hQ).clm_apply hP).add (by fun_prop)

theorem spatialSource_contDiffAt (g h : Field d) (Λ : ℂ) (x : Fin d → ℝ)
    (hg : ∀ i j, ContDiffAt ℝ 3 (fun y => g y i j) x)
    (hh : ∀ i j, ContDiffAt ℝ 3 (fun y => h y i j) x)
    (hdet : (g x).det ≠ 0) (k i j : Fin d) :
    ContDiffAt ℂ 2 (spatialSource g h Λ x k i j) 0 :=
  (spatialSourceModel_contDiffAt g h Λ x hdet k i j).congr_of_eventuallyEq
    (spatialSource_eventuallyEq g h Λ x hg hh hdet k i j)

theorem spatialSource_first (g h : Field d) (Λ : ℂ) (x : Fin d → ℝ)
    (hg : ∀ i j, ContDiffAt ℝ 3 (fun y => g y i j) x)
    (hh : ∀ i j, ContDiffAt ℝ 3 (fun y => h y i j) x)
    (hdet : (g x).det ≠ 0) (k i j : Fin d) :
    deriv (spatialSource g h Λ x k i j) 0 =
      coordDeriv k (fun y => linearField g h y i j+Λ*h y i j) x := by
  have hd : Matrix.det (amplitudeJet (jetSpace g x) (jetSpace h x) 0).1 ≠ 0 := by
    simpa [amplitudeJet,jetSpace,toSpace,twoJet] using hdet
  have hD := affineSpatialEinstein_hasDerivAt (jetSpace g x) (jetSpace h x)
    (jetSpacePartial g x k) (jetSpacePartial h x k) i j 0 hd
  have hC := (((hasDerivAt_id (0 : ℂ)).mul_const (coordDeriv k (fun y => h y i j) x)).const_add
    (coordDeriv k (fun y => g y i j) x)).const_mul Λ
  have hv : HasDerivAt (spatialSourceModel g h Λ x k i j)
      (affineSpatialSlope (jetSpace g x) (jetSpace h x)
        (jetSpacePartial g x k) (jetSpacePartial h x k) i j 0+
        Λ*coordDeriv k (fun y => h y i j) x) 0 := by
    convert! hD.add hC using 1
    simp
  rw [(spatialSource_eventuallyEq g h Λ x hg hh hdet k i j).deriv_eq,hv.deriv,
    coordDeriv_add (f := fun y => linearField g h y i j) (g := fun y => Λ*h y i j) (linearField_differentiableAt g h x hg hh hdet i j)
      ((differentiableAt_const Λ).mul ((hh i j).differentiableAt (by norm_num))),
    coordDeriv_mul (f := fun _ => Λ) (g := fun y => h y i j) (differentiableAt_const Λ) ((hh i j).differentiableAt (by norm_num)),
    linearField_coordDeriv g h x hg hh hdet]
  simp [coordDeriv]

theorem spatialSource_second (g h : Field d) (Λ : ℂ) (x : Fin d → ℝ)
    (hg : ∀ i j, ContDiffAt ℝ 3 (fun y => g y i j) x)
    (hh : ∀ i j, ContDiffAt ℝ 3 (fun y => h y i j) x)
    (hdet : (g x).det ≠ 0) (k i j : Fin d) :
    deriv (deriv (spatialSource g h Λ x k i j)) 0 =
      coordDeriv k (fun y => hessianField g h y i j) x := by
  have he := spatialSource_eventuallyEq g h Λ x hg hh hdet k i j
  let A := affineSpatialEinstein (jetSpace g x) (jetSpace h x)
    (jetSpacePartial g x k) (jetSpacePartial h x k) i j
  let C := fun e : ℂ => Λ*(coordDeriv k (fun y => g y i j) x+e*coordDeriv k (fun y => h y i j) x)
  have ha : ContDiffAt ℂ 2 A 0 := by
    have hm := spatialSourceModel_contDiffAt g h 0 x hdet k i j
    convert! hm using 1
    funext e
    simp only [spatialSourceModel,zero_mul,add_zero]
    rfl
  have hc : ContDiffAt ℂ 2 C 0 := by dsimp [C]; fun_prop
  have hz : deriv (deriv C) 0 = 0 := by
    have hder : deriv C = fun _ => Λ*coordDeriv k (fun y => h y i j) x := by
      funext e
      have hv := (((hasDerivAt_id e).mul_const (coordDeriv k (fun y => h y i j) x)).const_add
        (coordDeriv k (fun y => g y i j) x)).const_mul Λ
      convert! hv.deriv using 1
      simp
    rw [hder]; simp
  have hv := iteratedDeriv_fun_add ha hc
  simp only [show 2 = 1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_zero] at hv
  rw [he.deriv.deriv_eq]
  change deriv (deriv (fun e => A e+C e)) 0 = _
  rw [hv,hz,add_zero]
  rw [affineSpatialEinstein_second _ _ _ _ i j hdet,hessianField_coordDeriv g h x hg hh hdet]

end
end GaloisForLFunctions.HTGeometry.ComplexMetricField
