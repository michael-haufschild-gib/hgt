import GaloisForLFunctions.RHTower.SelbergMaassDilationRellich

/-!
# Original arithmetic phase losses satisfy the physical Rellich identity

Every phased three-block displacement is a fixed continuous linear observation
of the original Maass source. Its complete normalized squared coordinate sum is
exactly inversion-transfer loss, including for every physical source derivative.
The finite family of original Rellich identities therefore gives an arithmetic
radial/angular/mass balance with every side and top stress retained. Source
regularity identifies all three boundary energies with actual transfer-loss
integrals on the complete paired modular arc.
-/

open Complex Set UpperHalfPlane MeasureTheory
open scoped BigOperators ContDiff
namespace GaloisForLFunctions.RHTower.SelbergMaassPhaseRellich
open SelbergMaassCongruenceTrace SelbergMaassCongruenceAverage SelbergMaassCuspTransport
open SelbergMaassInversionGram SelbergMaassInversionPhaseEnergy SelbergMaassCharacterFourier
open SelbergMaassCharacterDynamics SelbergMaassCharacterSeamFlux SelbergMaassCharacterGradient
open SelbergMaassDilationStress SelbergMaassDilationRellich SelbergMaassTraceEnergy
open SelbergModularDomainSlices SelbergMaassMean SelbergMaassTraceStokes
open GaloisForLFunctions.HTGeometry
noncomputable section
local instance gammaNormal (N : ℕ) : (CongruenceSubgroup.Gamma (N+1)).Normal :=
  CongruenceSubgroup.Gamma_normal (N+1)

/-- Every three-block arithmetic phase and every original deck coordinate. -/
abbrev PhaseIndex (N : ℕ) := ZMod (N+1) × ZMod (N+1) × ZMod (N+1) × Deck N

/-- Literal coordinate observation of an original phased three-block displacement. -/
def phaseReadout (N : ℕ) (r s : ZMod (N+1)) (i : PhaseIndex N) :
    EuclideanSpace ℂ (Deck N) →L[ℂ] ℂ :=
  (EuclideanSpace.proj i.2.2.2).comp ((ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Deck N)))-
    tripleWeight N r s i.1 i.2.1 i.2.2.1 •
      (finiteRegularUnitary (deckTriple N i.1 i.2.1 i.2.2.1)).toLinearEquiv.toLinearMap.toContinuousLinearMap)

/-- The fixed observation is exactly the complete arithmetic displacement coordinate. -/
theorem phaseReadout_apply (N : ℕ) (r s a b c : ZMod (N+1)) (q : Deck N)
    (v : EuclideanSpace ℂ (Deck N)) :
    phaseReadout N r s (a,b,c,q) v = (v-tripleMotion N r s a b c v) q := rfl

/-- Actual normalized average over all phases and coordinates. -/
def phaseAverage (N : ℕ) (H : PhaseIndex N → ℝ) : ℝ :=
  ((((N+1 : ℕ) : ℝ)⁻¹)^3/2)*∑ i, H i

/-- The full squared observation average is exactly the original inversion-transfer loss. -/
theorem phaseAverage_norm (N : ℕ) (r s : ZMod (N+1)) (v : EuclideanSpace ℂ (Deck N)) :
    phaseAverage N (fun i => normSq (phaseReadout N r s i v)) =
      ‖v‖^2-‖inversionTransfer N r s v‖^2 := by
  have he (a b c : ZMod (N+1)) :
      (∑ q : Deck N, normSq (phaseReadout N r s (a,b,c,q) v)) =
      ‖v-tripleMotion N r s a b c v‖^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Complex.sq_norm]
    rfl
  unfold phaseAverage
  simp only [Fintype.sum_prod_type]
  simp_rw [he]
  exact triple_displacement_energy N r s v

variable (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N+1))) lam)
    (r s : ZMod (N+1))

/-- Actual arithmetic displacement observations commute with each physical source derivative. -/
theorem phaseReadout_dir (i : PhaseIndex N) (v : ℂ) (z : ℍ) :
    dir v (observedField N f (phaseReadout N r s i)) (z : ℂ) =
      phaseReadout N r s i (sourceDerivative N f v z) := by
  rw [sourceDerivative_eq_dir]
  exact source_readout_dir N f (phaseReadout N r s i) v z

/-- Complete physical derivative loss is the exact same arithmetic phase energy. -/
theorem phaseAverage_dir (v : ℂ) (z : ℍ) :
    phaseAverage N (fun i => normSq (dir v (observedField N f (phaseReadout N r s i)) (z : ℂ))) =
      ‖sourceDerivative N f v z‖^2-
        ‖inversionTransfer N r s (sourceDerivative N f v z)‖^2 := by
  simp_rw [phaseReadout_dir]
  exact phaseAverage_norm N r s _

/-- Complete radial boundary energy of all literal arithmetic displacements. -/
def radialPhaseBoundary : ℝ := phaseAverage N (fun i => radialBoundary N f (phaseReadout N r s i))
/-- Complete angular boundary energy of all literal arithmetic displacements. -/
def angularPhaseBoundary : ℝ := phaseAverage N (fun i => angularBoundary N f (phaseReadout N r s i))
/-- Complete inverse-cube weighted source mass of every arithmetic displacement. -/
def massPhaseBoundary : ℝ := phaseAverage N (fun i => massBoundary N f (phaseReadout N r s i))
/-- Both actual vertical sides retain their full arithmetic displacement stress. -/
def sidePhaseFlux (Y : ℝ) : ℝ := phaseAverage N (fun i => sideFlux N f (phaseReadout N r s i) Y)
/-- The full physical top stress of all original arithmetic displacements. -/
def topPhaseFlux (Y : ℝ) : ℝ := phaseAverage N (fun i => topFlux N f (phaseReadout N r s i) Y)

/-- Exact original arithmetic phase-loss Rellich balance, including every side and top stress. -/
theorem phase_rellich_identity {Y : ℝ} (hY : 1 ≤ Y) :
    radialPhaseBoundary N f r s+lam*massPhaseBoundary N f r s =
      angularPhaseBoundary N f r s+sidePhaseFlux N f r s Y+topPhaseFlux N f r s Y := by
  have h := Finset.sum_congr (s₁ := (Finset.univ : Finset (PhaseIndex N))) rfl
    (fun i _ => radial_potential_boundary_identity N f (phaseReadout N r s i) hY)
  simp only [Finset.sum_add_distrib,← Finset.mul_sum] at h
  unfold radialPhaseBoundary angularPhaseBoundary massPhaseBoundary sidePhaseFlux topPhaseFlux phaseAverage
  rw [show ((((N+1 : ℕ) : ℝ)⁻¹)^3/2)*(∑ i, radialBoundary N f (phaseReadout N r s i))+
      lam*(((((N+1 : ℕ) : ℝ)⁻¹)^3/2)*(∑ i, massBoundary N f (phaseReadout N r s i))) =
      ((((N+1 : ℕ) : ℝ)⁻¹)^3/2)*((∑ i, radialBoundary N f (phaseReadout N r s i))+
        lam*(∑ i, massBoundary N f (phaseReadout N r s i))) by ring,h]
  ring

/-- Actual phase mass is nonnegative for every original source and character pair. -/
theorem massPhaseBoundary_nonneg : 0 ≤ massPhaseBoundary N f r s := by
  apply mul_nonneg (by positivity)
  exact Finset.sum_nonneg (fun i _ => massBoundary_nonneg N f (phaseReadout N r s i))

/-- The exceptional original source satisfies its physical radial phase-energy estimate. -/
theorem radialPhaseBoundary_le (N : ℕ) (lam : Ioo (0 : ℝ) (1/4))
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N+1))) (lam : ℝ))
    (r s : ZMod (N+1)) :
    radialPhaseBoundary N f r s ≤
      angularPhaseBoundary N f r s+sidePhaseFlux N f r s 1+topPhaseFlux N f r s 1 := by
  have h := phase_rellich_identity N f r s (Y := 1) le_rfl
  have hn := mul_nonneg lam.property.1.le (massPhaseBoundary_nonneg N f r s)
  linarith

private theorem arc_weight_continuous {H : ℂ → ℝ}
    (hH : ContinuousOn H {w : ℂ | 0 < w.im}) (k : ℕ) :
    ContinuousOn (fun x => H (point x (arcHeight x))/(arcHeight x)^k)
      (Icc (-(1/2 : ℝ)) (1/2)) := by
  have hc : Continuous (fun x => point x (arcHeight x)) := by
    unfold point
    exact Complex.continuous_ofReal.add ((Complex.continuous_ofReal.comp continuous_arcHeight).mul continuous_const)
  exact (hH.comp hc.continuousOn (by
    intro x hx
    simpa [point] using arcHeight_pos hx)).div₀ (continuous_arcHeight.pow k).continuousOn
    (fun x hx => pow_ne_zero k (arcHeight_pos hx).ne')

private theorem observed_moving_energy_continuous
    (L : EuclideanSpace ℂ (Deck N) →L[ℂ] ℂ) (v : ℂ → ℂ) (hv : Continuous v) :
    ContinuousOn (fun w => normSq (dir (v w) (observedField N f L) w)) {w : ℂ | 0 < w.im} := by
  have hd := (readout_contDiffOn N f L).continuousOn_fderiv_of_isOpen isOpen_upperHalfPlaneSet
    (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  exact Complex.continuous_normSq.comp_continuousOn (hd.clm_apply hv.continuousOn)

private theorem radial_arc_continuous (i : PhaseIndex N) :
    ContinuousOn (radialArc N f (phaseReadout N r s i)) (Icc (-(1/2 : ℝ)) (1/2)) := by
  unfold radialArc
  simpa only [pow_one] using arc_weight_continuous
    (observed_moving_energy_continuous N f (phaseReadout N r s i) (fun w => w) continuous_id) 1

private theorem angular_arc_continuous (i : PhaseIndex N) :
    ContinuousOn (angularArc N f (phaseReadout N r s i)) (Icc (-(1/2 : ℝ)) (1/2)) := by
  unfold angularArc
  simpa only [pow_one] using arc_weight_continuous
    (observed_moving_energy_continuous N f (phaseReadout N r s i) (fun w => Complex.I*w)
      (continuous_const.mul continuous_id)) 1

private theorem mass_arc_continuous (i : PhaseIndex N) :
    ContinuousOn (massArc N f (phaseReadout N r s i)) (Icc (-(1/2 : ℝ)) (1/2)) := by
  exact arc_weight_continuous
    (Complex.continuous_normSq.comp_continuousOn (readout_contDiffOn N f (phaseReadout N r s i)).continuousOn) 3

private theorem paired_average_integral (N : ℕ) (H : PhaseIndex N → ℝ → ℝ)
    (hH : ∀ i, ContinuousOn (H i) (Icc (-(1/2 : ℝ)) (1/2))) :
    phaseAverage N (fun i => ∫ x in (0 : ℝ)..(1/2), H i x+H i (-x)) =
      ∫ x in (0 : ℝ)..(1/2), phaseAverage N (fun i => H i x)+phaseAverage N (fun i => H i (-x)) := by
  have hi (i : PhaseIndex N) : IntervalIntegrable (fun x => H i x+H i (-x)) volume 0 (1/2) := by
    have hr : ContinuousOn (fun x => H i (-x)) (Icc (-(1/2 : ℝ)) (1/2)) :=
      (hH i).comp continuous_neg.continuousOn
        (by intro x hx; constructor <;> linarith [hx.1,hx.2])
    apply (((hH i).add hr).mono _).intervalIntegrable
    intro x hx
    have hh : x ∈ Icc (0 : ℝ) (1/2) := by simpa using hx
    exact ⟨by linarith [hh.1],hh.2⟩
  unfold phaseAverage
  rw [← intervalIntegral.integral_finsetSum (fun i _ => hi i),← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x _
  simp only [Finset.sum_add_distrib,mul_add]

private theorem phaseAverage_div (N : ℕ) (H : PhaseIndex N → ℝ) (c : ℝ) :
    phaseAverage N (fun i => H i/c)=phaseAverage N H/c := by
  simp only [phaseAverage,Finset.sum_div,Finset.mul_sum,mul_div_assoc]

private theorem phaseAverage_dir_chart (v w : ℂ) (hw : 0 < w.im) :
    phaseAverage N (fun i => normSq (dir v (observedField N f (phaseReadout N r s i)) w)) =
      ‖dir v (fun t => sourceVector N f (ofComplex t)) w‖^2-
        ‖inversionTransfer N r s (dir v (fun t => sourceVector N f (ofComplex t)) w)‖^2 := by
  simpa only [sourceDerivative_eq_dir,ofComplex_apply_of_im_pos hw] using
    phaseAverage_dir N f r s v (ofComplex w)

/-- Actual inversion-transfer loss of the original radial derivative, with physical arc weight. -/
def radialPhaseDensity (x : ℝ) : ℝ :=
  let w := point x (arcHeight x)
  let v := dir w (fun t => sourceVector N f (ofComplex t)) w
  (‖v‖^2-‖inversionTransfer N r s v‖^2)/arcHeight x

/-- Actual inversion-transfer loss of the full original angular derivative. -/
def angularPhaseDensity (x : ℝ) : ℝ :=
  let w := point x (arcHeight x)
  let v := dir (Complex.I*w) (fun t => sourceVector N f (ofComplex t)) w
  (‖v‖^2-‖inversionTransfer N r s v‖^2)/arcHeight x

/-- Actual inversion-transfer loss of source mass with the original potential's arc weight. -/
def massPhaseDensity (x : ℝ) : ℝ :=
  let v := sourceVector N f (ofComplex (point x (arcHeight x)))
  (‖v‖^2-‖inversionTransfer N r s v‖^2)/(arcHeight x)^3

/-- Every original radial phase displacement is retained in the exact transfer-loss density. -/
theorem radialPhaseDensity_eq_average {x : ℝ} (hx : x ∈ Icc (-(1/2 : ℝ)) (1/2)) :
    phaseAverage N (fun i => radialArc N f (phaseReadout N r s i) x)=radialPhaseDensity N f r s x := by
  unfold radialArc radialPhaseDensity
  rw [phaseAverage_div,phaseAverage_dir_chart N f r s _ _ (by simpa [point] using arcHeight_pos hx)]

/-- Full angular phase displacement density equals the literal angular transfer loss. -/
theorem angularPhaseDensity_eq_average {x : ℝ} (hx : x ∈ Icc (-(1/2 : ℝ)) (1/2)) :
    phaseAverage N (fun i => angularArc N f (phaseReadout N r s i) x)=angularPhaseDensity N f r s x := by
  unfold angularArc angularPhaseDensity
  rw [phaseAverage_div,phaseAverage_dir_chart N f r s _ _ (by simpa [point] using arcHeight_pos hx)]

/-- Complete weighted phase mass is exactly the literal original transfer-loss density. -/
theorem massPhaseDensity_eq_average (x : ℝ) :
    phaseAverage N (fun i => massArc N f (phaseReadout N r s i) x)=massPhaseDensity N f r s x := by
  unfold massArc observedField massPhaseDensity
  rw [phaseAverage_div,phaseAverage_norm]

private theorem half_arc_pair {x : ℝ} (hx : x ∈ uIcc (0 : ℝ) (1/2)) :
    x ∈ Icc (-(1/2 : ℝ)) (1/2) ∧ -x ∈ Icc (-(1/2 : ℝ)) (1/2) := by
  have h : x ∈ Icc (0 : ℝ) (1/2) := by simpa using hx
  constructor <;> constructor <;> linarith [h.1,h.2]

/-- The complete radial phase boundary is the genuine integral of physical derivative transfer loss. -/
theorem radialPhaseBoundary_eq_loss_integral :
    radialPhaseBoundary N f r s = ∫ x in (0 : ℝ)..(1/2),
      radialPhaseDensity N f r s x+radialPhaseDensity N f r s (-x) := by
  change phaseAverage N (fun i => ∫ x in (0 : ℝ)..(1/2),
    radialArc N f (phaseReadout N r s i) x+radialArc N f (phaseReadout N r s i) (-x)) = _
  rw [paired_average_integral N _ (radial_arc_continuous N f r s)]
  apply intervalIntegral.integral_congr
  intro x hx
  have hp := half_arc_pair hx
  dsimp only
  rw [radialPhaseDensity_eq_average N f r s hp.1,radialPhaseDensity_eq_average N f r s hp.2]

/-- The complete angular phase boundary is exactly the integral of original angular transfer loss. -/
theorem angularPhaseBoundary_eq_loss_integral :
    angularPhaseBoundary N f r s = ∫ x in (0 : ℝ)..(1/2),
      angularPhaseDensity N f r s x+angularPhaseDensity N f r s (-x) := by
  change phaseAverage N (fun i => ∫ x in (0 : ℝ)..(1/2),
    angularArc N f (phaseReadout N r s i) x+angularArc N f (phaseReadout N r s i) (-x)) = _
  rw [paired_average_integral N _ (angular_arc_continuous N f r s)]
  apply intervalIntegral.integral_congr
  intro x hx
  have hp := half_arc_pair hx
  dsimp only
  rw [angularPhaseDensity_eq_average N f r s hp.1,angularPhaseDensity_eq_average N f r s hp.2]

/-- Every phase and source coordinate contributes to the exact weighted transfer-mass integral. -/
theorem massPhaseBoundary_eq_loss_integral :
    massPhaseBoundary N f r s = ∫ x in (0 : ℝ)..(1/2),
      massPhaseDensity N f r s x+massPhaseDensity N f r s (-x) := by
  change phaseAverage N (fun i => ∫ x in (0 : ℝ)..(1/2),
    massArc N f (phaseReadout N r s i) x+massArc N f (phaseReadout N r s i) (-x)) = _
  rw [paired_average_integral N _ (mass_arc_continuous N f r s)]
  apply intervalIntegral.integral_congr
  intro x _
  dsimp only
  rw [massPhaseDensity_eq_average,massPhaseDensity_eq_average]

/-- The original arithmetic transfer losses obey the full physical Rellich integral identity. -/
theorem phase_loss_rellich_integral :
    (∫ x in (0 : ℝ)..(1/2), radialPhaseDensity N f r s x+radialPhaseDensity N f r s (-x))+
      lam*(∫ x in (0 : ℝ)..(1/2), massPhaseDensity N f r s x+massPhaseDensity N f r s (-x)) =
    (∫ x in (0 : ℝ)..(1/2), angularPhaseDensity N f r s x+angularPhaseDensity N f r s (-x))+
      sidePhaseFlux N f r s 1+topPhaseFlux N f r s 1 := by
  rw [← radialPhaseBoundary_eq_loss_integral,← massPhaseBoundary_eq_loss_integral,
    ← angularPhaseBoundary_eq_loss_integral]
  exact phase_rellich_identity N f r s le_rfl

end
end GaloisForLFunctions.RHTower.SelbergMaassPhaseRellich
