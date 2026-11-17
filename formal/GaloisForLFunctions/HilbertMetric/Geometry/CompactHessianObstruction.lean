import GaloisForLFunctions.HilbertMetric.Geometry.SchwartzBonnetCharts
import GaloisForLFunctions.HilbertMetric.Geometry.SchwartzInversionAnalytic
import GaloisForLFunctions.HilbertMetric.Geometry.BonnetEnvelope
import GaloisForLFunctions.HilbertMetric.Geometry.SmoothSupportCompactification

/-!
# Nonanalyticity forced by a nowhere-scalar Hessian

A compactly supported planar function has zero Hessian outside its support.
Thus the explicit nowhere-scalar Schwartz potential has a noncompact tail.
Its smooth inverted correction consequently cannot be analytic at the pole.
-/

open Set Filter Topology
open scoped ContDiff
namespace GaloisForLFunctions.HilbertMetric.Geometry.CompactHessianObstruction
open GaloisForLFunctions.HTGeometry.GaussBonnet
open BonnetSupport SchwartzBonnetCharts SeparableHessian SchwartzInversionAnalytic
noncomputable section

/-- Every compactly supported planar function has a point with zero actual second partials. -/
theorem exists_zero_hessian_of_compactSupport {U : ℝ × ℝ → ℝ} (hU : HasCompactSupport U) :
    ∃ p, px (px U) p = 0 ∧ py (py U) p = 0 ∧ py (px U) p = 0 := by
  haveI : NoncompactSpace (ℝ × ℝ) := NormedSpace.noncompactSpace ℝ (ℝ × ℝ)
  have hne : tsupport U ≠ univ := by
    intro h
    have hc := hU.isCompact
    rw [h] at hc
    exact NoncompactSpace.noncompact_univ hc
  have hex : ∃ p, p ∉ tsupport U := by
    by_contra h
    apply hne
    ext p
    simp only [Set.mem_univ, iff_true]
    by_contra hp
    exact h ⟨p, hp⟩
  obtain ⟨p, hp⟩ := hex
  have hx : p ∉ tsupport (px U) := fun h => hp (tsupport_fderiv_apply_subset (𝕜 := ℝ) (1, 0) h)
  have hy : p ∉ tsupport (py U) := fun h => hp (tsupport_fderiv_apply_subset (𝕜 := ℝ) (0, 1) h)
  have hdx := fderiv_of_notMem_tsupport (𝕜 := ℝ) hx
  have hdy := fderiv_of_notMem_tsupport (𝕜 := ℝ) hy
  refine ⟨p, ?_, ?_, ?_⟩
  · change fderiv ℝ (px U) p (1, 0) = 0
    rw [hdx]; rfl
  · change fderiv ℝ (py U) p (0, 1) = 0
    rw [hdy]; rfl
  · change fderiv ℝ (px U) p (0, 1) = 0
    rw [hdx]; rfl

/-- The explicit Schwartz potential cannot have compact support. -/
theorem dampedSeed_not_compactSupport :
    ¬ HasCompactSupport (dampedSeedSchwartz : ℝ × ℝ → ℝ) := by
  intro h
  obtain ⟨p, hxx, hyy, hxy⟩ := exists_zero_hessian_of_compactSupport h
  have hs : px (px dampedSeedSchwartz) p = py (py dampedSeedSchwartz) p ∧
      py (px dampedSeedSchwartz) p = 0 := ⟨hxx.trans hyy.symm, hxy⟩
  exact south_radius_not_scalar p
    ((radius_scalar_iff (dampedSeedSchwartz.smooth ⊤) amplitude_pos.ne' p).mpr hs)

/-- The same explicit potential has a noncompact tail in complex coordinates. -/
theorem complexPotential_not_compactSupport :
    ¬ HasCompactSupport (complexPotential : ℂ → ℝ) := by
  intro h
  have hc := h.comp_homeomorph Complex.equivRealProdCLM.symm.toHomeomorph
  apply dampedSeed_not_compactSupport
  have he : (complexPotential : ℂ → ℝ) ∘ Complex.equivRealProdCLM.symm.toHomeomorph =
      (dampedSeedSchwartz : ℝ × ℝ → ℝ) := by
    funext p
    change dampedSeedSchwartz (Complex.equivRealProdCLM (Complex.equivRealProdCLM.symm p)) = _
    rw [ContinuousLinearEquiv.apply_symm_apply]
  rwa [he] at hc

/-- The explicit infinitely flat inversion germ is not real analytic. -/
theorem kelvin_not_analytic : ¬ AnalyticAt ℝ (SchwartzInversion.kelvin complexPotential) 0 :=
  fun h => complexPotential_not_compactSupport ((kelvin_analyticAt_iff complexPotential).mp h)

/-- The actual support correction is smooth and flat but nonanalytic at its added pole. -/
theorem northCorrection_not_analytic :
    ¬ AnalyticAt ℝ (SchwartzInversion.northCorrection complexPotential) 0 :=
  fun h => complexPotential_not_compactSupport ((northCorrection_analyticAt_iff complexPotential).mp h)

/-- The actual north support function is smooth but not real analytic at the pole. -/
theorem northSupport_not_analytic : ¬ AnalyticAt ℝ north 0 := by
  intro hn
  have hg : AnalyticAt ℝ (fun z : ℂ => amplitude⁻¹ * (north z - 1)) 0 :=
    (analyticAt_const : AnalyticAt ℝ (fun _ : ℂ => amplitude⁻¹) 0).mul (hn.sub analyticAt_const)
  have he : (fun z : ℂ => amplitude⁻¹ * (north z - 1)) =
      SchwartzInversion.northCorrection complexPotential := by
    funext z
    unfold north SchwartzInversion.northSupport
    calc
      amplitude⁻¹ * ((1 + amplitude * SchwartzInversion.northCorrection complexPotential z) - 1) =
          (amplitude⁻¹ * amplitude) * SchwartzInversion.northCorrection complexPotential z := by ring
      _ = _ := by rw [inv_mul_cancel₀ amplitude_pos.ne', one_mul]
  rw [he] at hg
  exact northCorrection_not_analytic hg

/-- The unperturbed inverse-coordinate sphere map is real analytic everywhere. -/
theorem round_north_analytic (z : ℂ) : AnalyticAt ℝ Bottcher.stereoInvExtended z := by
  have hd : ContDiff ℝ ω (fun z : ℂ => 1 + ‖z‖ ^ 2) :=
    contDiff_const.add (contDiff_norm_sq ℂ)
  have hp : ContDiff ℝ ω (fun z : ℂ =>
      (![2 * z.re / (1 + ‖z‖ ^ 2), -2 * z.im / (1 + ‖z‖ ^ 2),
        (1 - ‖z‖ ^ 2) / (1 + ‖z‖ ^ 2)] : Fin 3 → ℝ)) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i
    · exact (contDiff_const.mul Complex.reCLM.contDiff).div hd (fun z => by positivity)
    · exact (contDiff_const.mul Complex.imCLM.contDiff).div hd (fun z => by positivity)
    · exact (contDiff_const.sub (contDiff_norm_sq ℂ)).div hd (fun z => by positivity)
  have h := (EuclideanSpace.equiv (Fin 3) ℝ).symm.toContinuousLinearMap.contDiff.comp hp
  change ContDiff ℝ ω Bottcher.stereoInvExtended at h
  exact h.contDiffAt.analyticAt

/-- The actual north-chart surface has the previously constructed scalar support function. -/
theorem north_surface_support_height (z : ℂ) :
    inner ℝ (SmoothSupportCompactification.north dampedSeedSchwartz amplitude z)
      (Bottcher.stereoInvExtended z) = north z := by
  by_cases hz : z = 0
  · subst z
    rw [SmoothSupportCompactification.north_zero, Bottcher.stereoInvExtended_zero, north_zero]
    rw [PiLp.inner_apply, Fin.sum_univ_three]
    change (0 : ℝ) * 0 + 0 * 0 + 1 * 1 = 1
    norm_num
  · have hN : Bottcher.stereoInvExtended z =
        StereographicFrame.normal ((z⁻¹).re, (z⁻¹).im) := by
      change Bottcher.stereoInvExtended z = Bottcher.stereo z⁻¹
      simpa only [inv_inv] using
        (Bottcher.stereo_eq_stereoInvExtended_inv (inv_ne_zero hz)).symm
    rw [← SmoothSupportCompactification.chart_overlap dampedSeedSchwartz amplitude hz,
      hN, ← chart_overlap hz]
    change inner ℝ (BonnetSurface.surface south ((z⁻¹).re, (z⁻¹).im))
      (StereographicFrame.normal ((z⁻¹).re, (z⁻¹).im)) = south ((z⁻¹).re, (z⁻¹).im)
    exact BonnetEnvelope.surface_support_height south _

/-- The actual smooth surface chart is nonanalytic at its infinitely flat umbilic. -/
theorem north_surface_not_analytic :
    ¬ AnalyticAt ℝ (SmoothSupportCompactification.north dampedSeedSchwartz amplitude) 0 := by
  intro h
  have hc : ContDiffAt ℝ ω (SmoothSupportCompactification.north dampedSeedSchwartz amplitude) 0 :=
    h.contDiffAt
  have hr : ContDiffAt ℝ ω Bottcher.stereoInvExtended 0 := (round_north_analytic 0).contDiffAt
  have ha := (hc.inner ℝ hr).analyticAt
  have he : (fun z : ℂ => inner ℝ
      (SmoothSupportCompactification.north dampedSeedSchwartz amplitude z)
      (Bottcher.stereoInvExtended z)) = north := funext north_surface_support_height
  rw [he] at ha
  exact northSupport_not_analytic ha

#print axioms round_north_analytic
#print axioms north_surface_support_height
#print axioms north_surface_not_analytic
#print axioms northSupport_not_analytic
#print axioms complexPotential_not_compactSupport
#print axioms kelvin_not_analytic
#print axioms northCorrection_not_analytic
#print axioms exists_zero_hessian_of_compactSupport
#print axioms dampedSeed_not_compactSupport
end
end GaloisForLFunctions.HilbertMetric.Geometry.CompactHessianObstruction
