import GaloisForLFunctions.HilbertMetric.Geometry.CompactHessianObstruction

/-!
# Exact analyticity boundary for Schwartz support surfaces

A nonzero Schwartz perturbation has an analytic north chart exactly when
its planar potential has compact support. In that case the surface agrees
with the round sphere on a neighborhood of the pole.
-/

open Set Filter Topology
open scoped ContDiff
namespace GaloisForLFunctions.HilbertMetric.Geometry.SchwartzSurfaceAnalyticity
open GaloisForLFunctions.HTGeometry.GaussBonnet
open BonnetSupport BonnetSurface SchwartzSurfaceCorrection SchwartzInversion
open SchwartzInversionAnalytic SmoothSupportCompactification
noncomputable section

/-- A planar Schwartz potential in complex coordinates. -/
def complexPotential (f : SchwartzMap (ℝ × ℝ) ℝ) : SchwartzMap ℂ ℝ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℝ Complex.equivRealProdCLM f

theorem compact_complexPotential_iff (f : SchwartzMap (ℝ × ℝ) ℝ) :
    HasCompactSupport (complexPotential f : ℂ → ℝ) ↔ HasCompactSupport (f : ℝ × ℝ → ℝ) := by
  constructor
  · intro h
    have hc := h.comp_homeomorph Complex.equivRealProdCLM.symm.toHomeomorph
    have he : (complexPotential f : ℂ → ℝ) ∘ Complex.equivRealProdCLM.symm.toHomeomorph =
        (f : ℝ × ℝ → ℝ) := by
      funext p
      change f (Complex.equivRealProdCLM (Complex.equivRealProdCLM.symm p)) = f p
      rw [ContinuousLinearEquiv.apply_symm_apply]
    rwa [he] at hc
  · intro h
    exact h.comp_homeomorph Complex.equivRealProdCLM.toHomeomorph

/-- The actual vector surface has the scalar support obtained by Schwartz inversion. -/
theorem north_support_height (f : SchwartzMap (ℝ × ℝ) ℝ) (ε : ℝ) (z : ℂ) :
    inner ℝ (north f ε z) (Bottcher.stereoInvExtended z) = northSupport (complexPotential f) ε z := by
  by_cases hz : z = 0
  · subst z
    rw [north_zero, Bottcher.stereoInvExtended_zero]
    have hN : inner ℝ Bottcher.northPole Bottcher.northPole = 1 := by
      rw [PiLp.inner_apply, Fin.sum_univ_three]
      change (0 : ℝ) * 0 + 0 * 0 + 1 * 1 = 1
      norm_num
    rw [hN]
    simp [northSupport, northCorrection, kelvin_zero]
  · have hN : Bottcher.stereoInvExtended z =
        StereographicFrame.normal ((z⁻¹).re, (z⁻¹).im) := by
      change Bottcher.stereoInvExtended z = Bottcher.stereo z⁻¹
      simpa only [inv_inv] using
        (Bottcher.stereo_eq_stereoInvExtended_inv (inv_ne_zero hz)).symm
    rw [← SmoothSupportCompactification.chart_overlap f ε hz, hN,
      ← support_chart_overlap (complexPotential f) ε hz]
    change inner ℝ (surface (support f ε) ((z⁻¹).re, (z⁻¹).im))
      (StereographicFrame.normal ((z⁻¹).re, (z⁻¹).im)) = _
    rw [BonnetEnvelope.surface_support_height]
    simp only [support, inverseDenominator, southSupport, denominator,
      Complex.sq_norm, Complex.normSq_apply]
    change 1 + ε * (f ((z⁻¹).re, (z⁻¹).im) * (1 + (z⁻¹).re ^ 2 + (z⁻¹).im ^ 2)⁻¹) =
      1 + ε * f ((z⁻¹).re, (z⁻¹).im) / (1 + ((z⁻¹).re * (z⁻¹).re + (z⁻¹).im * (z⁻¹).im))
    congr 1
    ring

private theorem compact_displacement (f : SchwartzMap (ℝ × ℝ) ℝ)
    (hf : HasCompactSupport (f : ℝ × ℝ → ℝ)) :
    HasCompactSupport (displacement f : ℝ × ℝ → StereographicFrame.Space) := by
  apply HasCompactSupport.intro hf.isCompact
  intro p hp
  have h0 : f p = 0 := image_eq_zero_of_notMem_tsupport hp
  have hd := fderiv_of_notMem_tsupport (𝕜 := ℝ) hp
  have hx : px f p = 0 := by change fderiv ℝ f p (1, 0) = 0; rw [hd]; rfl
  have hy : py f p = 0 := by change fderiv ℝ f p (0, 1) = 0; rw [hd]; rfl
  rw [displacement_apply]
  simp [correction, h0, hx, hy]

/-- Compact planar support makes the actual north surface exactly round near its pole. -/
theorem north_eventually_round_of_compactSupport (f : SchwartzMap (ℝ × ℝ) ℝ) (ε : ℝ)
    (hf : HasCompactSupport (f : ℝ × ℝ → ℝ)) :
    north f ε =ᶠ[𝓝 0] Bottcher.stereoInvExtended := by
  have hd : HasCompactSupport (complexDisplacement f : ℂ → StereographicFrame.Space) :=
    (compact_displacement f hf).comp_homeomorph Complex.equivRealProdCLM.toHomeomorph
  have hs : HasCompactSupport ((ε • complexDisplacement f : SchwartzMap ℂ StereographicFrame.Space) :
      ℂ → StereographicFrame.Space) := hd.smul_left (f := fun _ : ℂ => ε)
  have hz := (kelvin_eventually_zero_iff (ε • complexDisplacement f)).mpr hs
  filter_upwards [hz] with z hz
  change Bottcher.stereoInvExtended z + kelvin (ε • complexDisplacement f) z = _
  rw [hz, add_zero]

/-- Analyticity at the pole is exactly compact planar support, apart from the zero perturbation. -/
theorem north_analyticAt_iff (f : SchwartzMap (ℝ × ℝ) ℝ) (ε : ℝ) :
    AnalyticAt ℝ (north f ε) 0 ↔ ε = 0 ∨ HasCompactSupport (f : ℝ × ℝ → ℝ) := by
  constructor
  · intro hn
    by_cases he : ε = 0
    · exact Or.inl he
    · right
      have hc : ContDiffAt ℝ ω (north f ε) 0 := hn.contDiffAt
      have hr : ContDiffAt ℝ ω Bottcher.stereoInvExtended 0 :=
        (CompactHessianObstruction.round_north_analytic 0).contDiffAt
      have ha := (hc.inner ℝ hr).analyticAt
      have hh : (fun z => inner ℝ (north f ε z) (Bottcher.stereoInvExtended z)) =
          northSupport (complexPotential f) ε := funext (north_support_height f ε)
      rw [hh] at ha
      have hg : AnalyticAt ℝ (fun z : ℂ => ε⁻¹ * (northSupport (complexPotential f) ε z - 1)) 0 :=
        (analyticAt_const : AnalyticAt ℝ (fun _ : ℂ => ε⁻¹) 0).mul (ha.sub analyticAt_const)
      have heq : (fun z : ℂ => ε⁻¹ * (northSupport (complexPotential f) ε z - 1)) =
          northCorrection (complexPotential f) := by
        funext z
        unfold northSupport
        calc
          ε⁻¹ * ((1 + ε * northCorrection (complexPotential f) z) - 1) =
              (ε⁻¹ * ε) * northCorrection (complexPotential f) z := by ring
          _ = _ := by rw [inv_mul_cancel₀ he, one_mul]
      rw [heq] at hg
      exact (compact_complexPotential_iff f).mp
        ((northCorrection_analyticAt_iff (complexPotential f)).mp hg)
  · rintro (rfl | hf)
    · have he : north f 0 = Bottcher.stereoInvExtended := by
        funext z
        simp [north, kelvin]
      rw [he]
      exact CompactHessianObstruction.round_north_analytic 0
    · exact (CompactHessianObstruction.round_north_analytic 0).congr
        (north_eventually_round_of_compactSupport f ε hf).symm

/-- Analytic north charts are precisely the germs that are already round. -/
theorem north_analyticAt_iff_eventually_round (f : SchwartzMap (ℝ × ℝ) ℝ) (ε : ℝ) :
    AnalyticAt ℝ (north f ε) 0 ↔ north f ε =ᶠ[𝓝 0] Bottcher.stereoInvExtended := by
  constructor
  · intro h
    rcases (north_analyticAt_iff f ε).mp h with rfl | hf
    · apply Filter.Eventually.of_forall
      intro z
      simp [north, kelvin]
    · exact north_eventually_round_of_compactSupport f ε hf
  · intro h
    exact (CompactHessianObstruction.round_north_analytic 0).congr h.symm

#print axioms north_support_height
#print axioms north_eventually_round_of_compactSupport
#print axioms north_analyticAt_iff
#print axioms north_analyticAt_iff_eventually_round
end
end GaloisForLFunctions.HilbertMetric.Geometry.SchwartzSurfaceAnalyticity
