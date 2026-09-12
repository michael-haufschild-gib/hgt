import GaloisForLFunctions.HTGeometry.ComplexMetricMixedEinsteinDerivative
import GaloisForLFunctions.HTGeometry.ComplexMetricEinsteinConservation

set_option autoImplicit false
namespace GaloisForLFunctions.HTGeometry.ComplexMetricField
open ScalarTwoJet ComplexCoordinateMetricTwoJet Filter Topology
open scoped ContDiff
noncomputable section
variable {d : ℕ}
local notation "Space" => ComplexMetricTwoJetSpace d

/-- First variation of the original Einstein field on actual metric jets. -/
def linearField (g h : Field d) (x : Fin d → ℝ) (i j : Fin d) : ℂ :=
  fderiv ℂ (einsteinComponent i j) (jetSpace g x) (jetSpace h x)

theorem linearField_differentiableAt (g h : Field d) (x : Fin d → ℝ)
    (hg : ∀ i j, ContDiffAt ℝ 3 (fun y => g y i j) x)
    (hh : ∀ i j, ContDiffAt ℝ 3 (fun y => h y i j) x)
    (hdet : (g x).det ≠ 0) (i j : Fin d) :
    DifferentiableAt ℝ (fun y => linearField g h y i j) x := by
  have hA := (contDiffAt_einsteinComponent (n := 2) (jetSpace g x) hdet i j).fderiv_right
    (m := 1) (by norm_num)
  have hF : ContDiffAt ℂ 1 (fun z : Space × Space => z.1) (jetSpace g x,jetSpace h x) := contDiffAt_fst
  have hP : ContDiffAt ℂ 1 (fun z : Space × Space => z.2) (jetSpace g x,jetSpace h x) := contDiffAt_snd
  have hS := (hA.comp (jetSpace g x,jetSpace h x) hF).clm_apply hP
  have hR := (hS.differentiableAt (by norm_num)).restrictScalars ℝ
  convert! hR.comp x ((jetSpace_differentiableAt g x hg).prodMk
    (jetSpace_differentiableAt h x hh)) using 1

local instance real_clm_continuousSMul {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F] :
    ContinuousSMul ℝ (E →L[ℂ] F) := IsScalarTower.continuousSMul ℂ

private theorem clm_apply_real {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F]
    {c : ℝ → E →L[ℂ] F} {c' : E →L[ℂ] F} {u : ℝ → E} {u' : E} {t : ℝ}
    (hc : HasDerivAt c c' t) (hu : HasDerivAt u u' t) :
    HasDerivAt (fun x => c x (u x)) (c' (u t)+c t u') t := by
  have he := (isBoundedBilinearMap_apply (𝕜 := ℂ) (E := E) (F := F)).hasFDerivAt (c t,u t)
  have hh := (he.restrictScalars ℝ).comp_hasDerivAt t (HasDerivAt.prodMk hc hu)
  simpa [Function.comp_def,IsBoundedBilinearMap.deriv,add_comm] using hh

private theorem firstVariation_hasDerivAt_real {q p : ℝ → Space} {q' p' : Space} {t : ℝ}
    (hq : HasDerivAt q q' t) (hp : HasDerivAt p p' t)
    (hdet : Matrix.det (q t).1 ≠ 0) (i j : Fin d) :
    HasDerivAt (fun z => fderiv ℂ (einsteinComponent i j) (q z) (p z))
      (secondVariation (q t) i j q' (p t)+fderiv ℂ (einsteinComponent i j) (q t) p') t := by
  have hA := (contDiffAt_einsteinComponent (n := 2) (q t) hdet i j).fderiv_right
    (m := 1) (by norm_num)
  have hD : HasFDerivAt (fderiv ℂ (einsteinComponent i j)) (secondVariation (q t) i j) (q t) :=
    (hA.differentiableAt (by norm_num)).hasFDerivAt
  have hR := HasFDerivAt.restrictScalars (𝕜' := ℂ) (E := Space) (F := Space →L[ℂ] ℂ) ℝ hD
  have hv := clm_apply_real (hR.comp_hasDerivAt t hq) hp
  convert! hv using 1

theorem linearField_coordDeriv (g h : Field d) (x : Fin d → ℝ)
    (hg : ∀ i j, ContDiffAt ℝ 3 (fun y => g y i j) x)
    (hh : ∀ i j, ContDiffAt ℝ 3 (fun y => h y i j) x)
    (hdet : (g x).det ≠ 0) (k i j : Fin d) :
    coordDeriv k (fun y => linearField g h y i j) x =
      affineSpatialSlope (jetSpace g x) (jetSpace h x)
        (jetSpacePartial g x k) (jetSpacePartial h x k) i j 0 := by
  have hd : Matrix.det (jetSpace g (coordinateLine x k 0)).1 ≠ 0 := by
    change (g (coordinateLine x k 0)).det ≠ 0
    simpa only [coordinateLine,zero_smul,add_zero] using hdet
  have hv := firstVariation_hasDerivAt_real (jetSpace_coordinateLine_hasDerivAt g x hg k)
    (jetSpace_coordinateLine_hasDerivAt h x hh k) hd i j
  have hu := (field_coordinateLine_hasDerivAt
    (linearField_differentiableAt g h x hg hh hdet i j) k).unique hv
  simp only [coordinateLine,zero_smul,add_zero] at hu
  rw [secondVariation_symm (jetSpace g x) hdet i j] at hu
  simpa only [affineSpatialSlope,amplitudeJet,zero_smul,add_zero] using hu

/-- Original full cosmological source along an actual affine metric field. -/
def affineSource (g h : Field d) (Λ : ℂ) (x : Fin d → ℝ) (i j : Fin d) (e : ℂ) : ℂ :=
  literalEinstein (affineField g h e) Λ x i j

theorem affineSource_eq (g h : Field d) (Λ : ℂ) (x : Fin d → ℝ)
    (hg : ∀ i j, ContDiffAt ℝ 2 (fun y => g y i j) x)
    (hh : ∀ i j, ContDiffAt ℝ 2 (fun y => h y i j) x) (i j : Fin d) (e : ℂ) :
    affineSource g h Λ x i j e =
      einsteinComponent i j (amplitudeJet (jetSpace g x) (jetSpace h x) e)+
        Λ*(g x i j+e*h x i j) := by
  change einsteinComponent i j (jetSpace (affineField g h e) x)+Λ*(g x i j+e*h x i j) = _
  rw [show jetSpace (affineField g h e) x = _ from jetSpace_add_smul g h x e hg hh]
  rfl

theorem affineSource_contDiffAt (g h : Field d) (Λ : ℂ) (x : Fin d → ℝ)
    (hg : ∀ i j, ContDiffAt ℝ 2 (fun y => g y i j) x)
    (hh : ∀ i j, ContDiffAt ℝ 2 (fun y => h y i j) x)
    (hdet : (g x).det ≠ 0) (i j : Fin d) {n : ℕ∞ω} :
    ContDiffAt ℂ n (affineSource g h Λ x i j) 0 := by
  have he : affineSource g h Λ x i j = fun e =>
      einsteinComponent i j (amplitudeJet (jetSpace g x) (jetSpace h x) e)+
        Λ*(g x i j+e*h x i j) := funext (affineSource_eq g h Λ x hg hh i j)
  rw [he]
  have hQ : ContDiffAt ℂ n (amplitudeJet (jetSpace g x) (jetSpace h x)) 0 := by
    unfold amplitudeJet; fun_prop
  have hd : Matrix.det (amplitudeJet (jetSpace g x) (jetSpace h x) 0).1 ≠ 0 := by
    simpa [amplitudeJet,jetSpace,toSpace,twoJet] using hdet
  exact ((contDiffAt_einsteinComponent _ hd i j).comp 0 hQ).add (by fun_prop)

theorem affineSource_hasDerivAt (g h : Field d) (Λ : ℂ) (x : Fin d → ℝ)
    (hg : ∀ i j, ContDiffAt ℝ 2 (fun y => g y i j) x)
    (hh : ∀ i j, ContDiffAt ℝ 2 (fun y => h y i j) x)
    (e : ℂ) (hdet : Matrix.det (amplitudeJet (jetSpace g x) (jetSpace h x) e).1 ≠ 0)
    (i j : Fin d) :
    HasDerivAt (affineSource g h Λ x i j)
      (fderiv ℂ (einsteinComponent i j) (amplitudeJet (jetSpace g x) (jetSpace h x) e)
        (jetSpace h x)+Λ*h x i j) e := by
  rw [funext (affineSource_eq g h Λ x hg hh i j)]
  have hD := ((contDiffAt_einsteinComponent (n := 1) _ hdet i j).differentiableAt
    (by norm_num)).hasFDerivAt.comp_hasDerivAt e
      (amplitudeJet_hasDerivAt (jetSpace g x) (jetSpace h x) e)
  have hc : HasDerivAt (fun z : ℂ => Λ*(g x i j+z*h x i j)) (Λ*h x i j) e := by
    convert! (((hasDerivAt_id e).mul_const (h x i j)).const_add (g x i j)).const_mul Λ using 1
    simp
  exact hD.add hc

theorem affineSource_first (g h : Field d) (Λ : ℂ) (x : Fin d → ℝ)
    (hg : ∀ i j, ContDiffAt ℝ 2 (fun y => g y i j) x)
    (hh : ∀ i j, ContDiffAt ℝ 2 (fun y => h y i j) x)
    (hdet : (g x).det ≠ 0) (i j : Fin d) :
    deriv (affineSource g h Λ x i j) 0 = linearField g h x i j+Λ*h x i j := by
  have hd : Matrix.det (amplitudeJet (jetSpace g x) (jetSpace h x) 0).1 ≠ 0 := by
    simpa only [amplitudeJet,zero_smul,add_zero,jetSpace,toSpace,twoJet] using hdet
  simpa only [amplitudeJet,zero_smul,add_zero,linearField] using
    (affineSource_hasDerivAt g h Λ x hg hh 0 hd i j).deriv

theorem affineSource_second (g h : Field d) (Λ : ℂ) (x : Fin d → ℝ)
    (hg : ∀ i j, ContDiffAt ℝ 2 (fun y => g y i j) x)
    (hh : ∀ i j, ContDiffAt ℝ 2 (fun y => h y i j) x)
    (hdet : (g x).det ≠ 0) (i j : Fin d) :
    deriv (deriv (affineSource g h Λ x i j)) 0 = hessianField g h x i j := by
  let slope := fun e => fderiv ℂ (einsteinComponent i j)
    (amplitudeJet (jetSpace g x) (jetSpace h x) e) (jetSpace h x)+Λ*h x i j
  have hc : Continuous (fun e => Matrix.det (amplitudeJet (jetSpace g x) (jetSpace h x) e).1) := by
    simp only [Matrix.det_apply',amplitudeJet,Prod.fst_add]; fun_prop
  have hd : Matrix.det (amplitudeJet (jetSpace g x) (jetSpace h x) 0).1 ≠ 0 := by
    simpa only [amplitudeJet,zero_smul,add_zero,jetSpace,toSpace,twoJet] using hdet
  have he : deriv (affineSource g h Λ x i j) =ᶠ[𝓝 0] slope := by
    filter_upwards [hc.continuousAt.eventually_ne hd] with e he
    exact (affineSource_hasDerivAt g h Λ x hg hh e he i j).deriv
  have hA := (contDiffAt_einsteinComponent (n := 2)
    (amplitudeJet (jetSpace g x) (jetSpace h x) 0) hd i j).fderiv_right
      (m := 1) (by norm_num)
  have hD := (hA.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt 0
    (amplitudeJet_hasDerivAt (jetSpace g x) (jetSpace h x) 0)
  have hv := (hD.clm_apply (hasDerivAt_const 0 (jetSpace h x))).add_const (Λ*h x i j)
  have hv' : HasDerivAt slope (hessianField g h x i j) 0 := by
    convert! hv using 1
    simp only [hessianField,secondVariation,amplitudeJet,zero_smul,add_zero,
      Function.comp_def,map_zero]
  rw [he.deriv_eq,hv'.deriv]

end
end GaloisForLFunctions.HTGeometry.ComplexMetricField
