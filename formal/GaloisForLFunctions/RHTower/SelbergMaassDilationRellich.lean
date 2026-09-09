import GaloisForLFunctions.RHTower.SelbergMaassDilationStress
import GaloisForLFunctions.RHTower.SelbergModularCurrentGreen

/-!
# Original Maass Rellich identity on the complete modular core

Integrating the actual conserved dilation stress gives a boundary identity with
radial energy, angular energy, inverse-cube weighted mass, and the full side and
top fluxes. All densities come from fixed linear observations of the original
Maass source. Source regularity proves every needed integral is well defined.
Positive exceptional spectral mass yields a radial-energy bound at unit height.
-/

open Complex Set Filter Topology MeasureTheory UpperHalfPlane
open scoped ContDiff
namespace GaloisForLFunctions.RHTower.SelbergMaassDilationRellich
open SelbergMaassCongruenceTrace SelbergMaassCuspTransport SelbergMaassCongruenceAverage
open SelbergMaassDilationStress SelbergModularCurrentGreen SelbergModularDomainSlices
open SelbergMaassMean SelbergMaassTraceStokes SelbergMaassTraceEnergy
noncomputable section
local instance gammaNormal (N : ℕ) : (CongruenceSubgroup.Gamma (N+1)).Normal :=
  CongruenceSubgroup.Gamma_normal (N+1)

variable (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N+1))) lam)
    (L : EuclideanSpace ℂ (Deck N) →L[ℂ] ℂ)

/-- The actual dilation-stress jump across both vertical sides of the modular core. -/
def sideFlux (Y : ℝ) : ℝ :=
  ∫ y in arcFloor..Y, dilationX N f L (point (1/2) y)-dilationX N f L (point (-(1/2)) y)

/-- The actual dilation-stress flux across the physical horizontal cutoff. -/
def topFlux (Y : ℝ) : ℝ :=
  ∫ x in (-(1/2 : ℝ))..(1/2), dilationY N f L (point x Y)

/-- Full Green integration of the original conserved dilation current retains every core boundary. -/
theorem core_dilation_green_identity {Y : ℝ} (hY : 1 ≤ Y) :
    sideFlux N f L Y+topFlux N f L Y+
      (∫ x in (0 : ℝ)..(1/2), circleStressFlux N f L x (arcHeight x)+
        circleStressFlux N f L (-x) (arcHeight x))=0 := by
  have h := current_green_identity (dilationX N f L) (dilationX_contDiffOn N f L)
    (dilationY N f L) (dilationY_contDiffOn N f L) hY
  have hz : (∫ p in domain Y, dir 1 (dilationX N f L) (point p.1 p.2)+
      dir Complex.I (dilationY N f L) (point p.1 p.2))=0 := by
    have he : (∫ p in domain Y, dir 1 (dilationX N f L) (point p.1 p.2)+
        dir Complex.I (dilationY N f L) (point p.1 p.2))=∫ _p in domain Y, (0 : ℝ) := by
      apply setIntegral_congr_fun (isCompact_domain Y).measurableSet
      intro p hp
      have hy : 0 < p.2 := by have hh := (domain_subset_cell Y hp).2.1; linarith
      have hd := dilation_conservation N f L (ofComplex (point p.1 p.2))
      simpa only [SelbergMaassUnipotentPaths.coe_ofComplex_point p.1 hy] using hd
    rw [he]
    simp
  rw [hz] at h
  have he : (∫ x in (0 : ℝ)..(1/2), normalPair (dilationX N f L) (dilationY N f L) x) =
      ∫ x in (0 : ℝ)..(1/2), circleStressFlux N f L x (arcHeight x)+circleStressFlux N f L (-x) (arcHeight x) := by
    apply intervalIntegral.integral_congr
    intro x _
    unfold normalPair circleStressFlux
    ring
  rw [he] at h
  exact h.symm

/-- Actual radial minus angular boundary energy, with original spectral mass and normal-density factor. -/
def arcStressEnergy (x : ℝ) : ℝ :=
  (normSq (dir (point x (arcHeight x)) (observedField N f L) (point x (arcHeight x)))-
    normSq (dir (Complex.I*point x (arcHeight x)) (observedField N f L) (point x (arcHeight x)))+
    (lam/(arcHeight x)^2)*normSq (observedField N f L (point x (arcHeight x))))/arcHeight x

/-- The complete physical boundary energy is exactly the inward dilation-stress flux. -/
theorem arcStressEnergy_eq_neg_flux {x : ℝ} (hx : x ∈ Icc (-(1/2 : ℝ)) (1/2)) :
    circleStressFlux N f L x (arcHeight x) = -arcStressEnergy N f L x := by
  have h := circleStressFlux_eq_energies N f L (x := x) (y := arcHeight x) (arcHeight_pos hx) (by rw [arcHeight_sq hx]; ring)
  simpa only [arcStressEnergy,neg_div] using h

/-- The original Maass Rellich identity on the full modular core retains physical angular energy and both side traces. -/
theorem core_rellich_identity {Y : ℝ} (hY : 1 ≤ Y) :
    (∫ x in (0 : ℝ)..(1/2), arcStressEnergy N f L x+arcStressEnergy N f L (-x)) =
      sideFlux N f L Y+topFlux N f L Y := by
  have h := core_dilation_green_identity N f L hY
  have he : (∫ x in (0 : ℝ)..(1/2), circleStressFlux N f L x (arcHeight x)+
      circleStressFlux N f L (-x) (arcHeight x)) =
      -(∫ x in (0 : ℝ)..(1/2), arcStressEnergy N f L x+arcStressEnergy N f L (-x)) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro x hx
    have hxI : x ∈ Icc (0 : ℝ) (1/2) := by simpa using hx
    have hp : x ∈ Icc (-(1/2 : ℝ)) (1/2) := ⟨by linarith [hxI.1],hxI.2⟩
    have hn : -x ∈ Icc (-(1/2 : ℝ)) (1/2) := ⟨by linarith [hxI.2],by linarith [hxI.1]⟩
    have ha : arcHeight (-x)=arcHeight x := by simp [arcHeight]
    dsimp only
    rw [arcStressEnergy_eq_neg_flux N f L hp]
    have hm := arcStressEnergy_eq_neg_flux N f L hn
    rw [ha] at hm
    rw [hm]
    ring
  rw [he] at h
  linarith

/-- The complete original core Rellich identity at unit height requires no extra cutoff premise. -/
theorem core_rellich_identity_one :
    (∫ x in (0 : ℝ)..(1/2), arcStressEnergy N f L x+arcStressEnergy N f L (-x)) =
      sideFlux N f L 1+topFlux N f L 1 := core_rellich_identity N f L le_rfl

private theorem observed_regular : ContDiffOn ℝ 2 (observedField N f L) {w : ℂ | 0 < w.im} :=
  SelbergMaassCharacterGradient.readout_contDiffOn N f L

private theorem radial_continuousOn :
    ContinuousOn (fun w => normSq (dir w (observedField N f L) w)) {w : ℂ | 0 < w.im} := by
  have hd := (observed_regular N f L).continuousOn_fderiv_of_isOpen isOpen_upperHalfPlaneSet
    (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  exact Complex.continuous_normSq.comp_continuousOn (hd.clm_apply continuousOn_id)

private theorem angular_continuousOn :
    ContinuousOn (fun w => normSq (dir (Complex.I*w) (observedField N f L) w)) {w : ℂ | 0 < w.im} := by
  have hd := (observed_regular N f L).continuousOn_fderiv_of_isOpen isOpen_upperHalfPlaneSet
    (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  exact Complex.continuous_normSq.comp_continuousOn
    (hd.clm_apply (continuous_const.mul continuous_id).continuousOn)

private theorem arc_quotient_continuousOn {H : ℂ → ℝ}
    (hH : ContinuousOn H {w : ℂ | 0 < w.im}) (k : ℕ) :
    ContinuousOn (fun x => H (point x (arcHeight x))/(arcHeight x)^k)
      (Icc (-(1/2 : ℝ)) (1/2)) := by
  have hc : Continuous (fun x => point x (arcHeight x)) := by
    unfold point
    exact Complex.continuous_ofReal.add ((Complex.continuous_ofReal.comp continuous_arcHeight).mul continuous_const)
  have hm : MapsTo (fun x => point x (arcHeight x)) (Icc (-(1/2 : ℝ)) (1/2)) {w : ℂ | 0 < w.im} := by
    intro x hx
    simpa [point] using arcHeight_pos hx
  exact (hH.comp hc.continuousOn hm).div₀ (continuous_arcHeight.pow k).continuousOn
    (fun x hx => pow_ne_zero k (arcHeight_pos hx).ne')

/-- Literal radial derivative energy with the physical circle normal-density weight. -/
def radialArc (x : ℝ) : ℝ :=
  normSq (dir (point x (arcHeight x)) (observedField N f L) (point x (arcHeight x)))/arcHeight x

/-- Literal angular derivative energy with the same physical circle weight. -/
def angularArc (x : ℝ) : ℝ :=
  normSq (dir (Complex.I*point x (arcHeight x)) (observedField N f L) (point x (arcHeight x)))/arcHeight x

/-- Original source mass with the inverse-cube height weight forced by dilation stress. -/
def massArc (x : ℝ) : ℝ := normSq (observedField N f L (point x (arcHeight x)))/(arcHeight x)^3

private theorem radialArc_continuousOn :
    ContinuousOn (radialArc N f L) (Icc (-(1/2 : ℝ)) (1/2)) := by
  unfold radialArc
  simpa only [pow_one] using arc_quotient_continuousOn (radial_continuousOn N f L) 1

private theorem angularArc_continuousOn :
    ContinuousOn (angularArc N f L) (Icc (-(1/2 : ℝ)) (1/2)) := by
  unfold angularArc
  simpa only [pow_one] using arc_quotient_continuousOn (angular_continuousOn N f L) 1

private theorem massArc_continuousOn :
    ContinuousOn (massArc N f L) (Icc (-(1/2 : ℝ)) (1/2)) :=
  arc_quotient_continuousOn
    (Complex.continuous_normSq.comp_continuousOn (observed_regular N f L).continuousOn) 3

private theorem pair_intervalIntegrable {H : ℝ → ℝ}
    (hH : ContinuousOn H (Icc (-(1/2 : ℝ)) (1/2))) :
    IntervalIntegrable (fun x => H x+H (-x)) volume 0 (1/2) := by
  have hr : ContinuousOn (fun x => H (-x)) (Icc (-(1/2 : ℝ)) (1/2)) :=
    hH.comp continuous_neg.continuousOn
    (by intro x hx; constructor <;> linarith [hx.1,hx.2])
  apply ((hH.add hr).mono _).intervalIntegrable
  intro x hx
  have hi : x ∈ Icc (0 : ℝ) (1/2) := by simpa using hx
  exact ⟨by linarith [hi.1],hi.2⟩

/-- Complete physical radial energy of both points on the paired modular arc. -/
def radialBoundary : ℝ := ∫ x in (0 : ℝ)..(1/2), radialArc N f L x+radialArc N f L (-x)

/-- Complete original angular derivative energy on the paired modular arc. -/
def angularBoundary : ℝ := ∫ x in (0 : ℝ)..(1/2), angularArc N f L x+angularArc N f L (-x)

/-- Complete actual inverse-cube weighted source mass on the paired arc. -/
def massBoundary : ℝ := ∫ x in (0 : ℝ)..(1/2), massArc N f L x+massArc N f L (-x)

/-- The original stress energy splits into radial, angular, and spectral-mass densities exactly. -/
theorem arcStressEnergy_split (x : ℝ) :
    arcStressEnergy N f L x = radialArc N f L x-angularArc N f L x+lam*massArc N f L x := by
  unfold arcStressEnergy radialArc angularArc massArc
  simp only [div_eq_mul_inv]
  ring

/-- The original weighted arc mass is nonnegative, with no source nonvanishing premise. -/
theorem massBoundary_nonneg : 0 ≤ massBoundary N f L := by
  apply intervalIntegral.integral_nonneg_of_forall (by norm_num : (0 : ℝ) ≤ 1/2)
  intro x
  have hn (t : ℝ) : 0 ≤ massArc N f L t :=
    div_nonneg (normSq_nonneg _) (pow_nonneg (Real.sqrt_nonneg _) 3)
  exact add_nonneg (hn x) (hn (-x))

/-- The full original radial-plus-potential boundary energy equals angular energy and actual side/top stress. -/
theorem radial_potential_boundary_identity {Y : ℝ} (hY : 1 ≤ Y) :
    radialBoundary N f L+lam*massBoundary N f L =
      angularBoundary N f L+sideFlux N f L Y+topFlux N f L Y := by
  have hiR := pair_intervalIntegrable (radialArc_continuousOn N f L)
  have hiA := pair_intervalIntegrable (angularArc_continuousOn N f L)
  have hiM := pair_intervalIntegrable (massArc_continuousOn N f L)
  have he : (∫ x in (0 : ℝ)..(1/2), arcStressEnergy N f L x+arcStressEnergy N f L (-x)) =
      radialBoundary N f L-angularBoundary N f L+lam*massBoundary N f L := by
    have hfun : (fun x => arcStressEnergy N f L x+arcStressEnergy N f L (-x)) =
        (fun x => ((radialArc N f L x+radialArc N f L (-x))-
          (angularArc N f L x+angularArc N f L (-x)))+lam*(massArc N f L x+massArc N f L (-x))) := by
      funext x
      rw [arcStressEnergy_split,arcStressEnergy_split]
      ring
    rw [hfun,intervalIntegral.integral_add (hiR.sub hiA) (hiM.const_mul lam),
      intervalIntegral.integral_sub hiR hiA,intervalIntegral.integral_const_mul]
    rfl
  have h := core_rellich_identity N f L hY
  rw [he] at h
  linarith

/-- For an exceptional original Maass source the radial arc energy is controlled by actual angular and boundary stress. -/
theorem radial_boundary_le (N : ℕ) (lam : Ioo (0 : ℝ) (1/4))
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N+1))) (lam : ℝ))
    (L : EuclideanSpace ℂ (Deck N) →L[ℂ] ℂ) :
    radialBoundary N f L ≤ angularBoundary N f L+sideFlux N f L 1+topFlux N f L 1 := by
  have h := radial_potential_boundary_identity N f L (Y := 1) le_rfl
  have hn := mul_nonneg lam.property.1.le (massBoundary_nonneg N f L)
  linarith

end
end GaloisForLFunctions.RHTower.SelbergMaassDilationRellich
