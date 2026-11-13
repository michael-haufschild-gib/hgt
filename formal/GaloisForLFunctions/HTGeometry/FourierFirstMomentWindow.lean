import GaloisForLFunctions.HTGeometry.FourierTailSup
import GaloisForLFunctions.HTGeometry.FourierIntegralDilation
import GaloisForLFunctions.HTGeometry.IntegralCauchySchwarz
import GaloisForLFunctions.RHTower.FourierPlancherelIntegral

/-!
# Fourier windows controlled by physical first moments

A spatial cutoff separates a bounded L¹ contribution from a small L² tail.
Plancherel then excludes concentration at frequency zero uniformly over
unit profiles with bounded first moment.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped FourierTransform
namespace GaloisForLFunctions.HTGeometry
private theorem interval_norm_integral_sq_le {f : ℝ → ℂ}
    (hf1 : Integrable f) (hf2 : MemLp f 2 volume)
    (hm : (∫ u, ‖f u‖ ^ 2) = 1) {H : ℝ} (hH : 0 < H) :
    (∫ u in Icc (-H) H, ‖f u‖) ^ 2 ≤ 2 * H := by
  have hs : Integrable (fun u => ‖f u‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm hf1.aestronglyMeasurable).mp hf2
  have hc : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Icc (-H) H) :=
    integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  have hcs := sq_integral_mul_le (μ := volume.restrict (Icc (-H) H))
    (f := fun u => ‖f u‖) (g := fun _ : ℝ => (1 : ℝ))
    hf1.aestronglyMeasurable.norm.restrict
    aestronglyMeasurable_const hs.integrableOn (by
      change IntegrableOn (fun _ : ℝ => (1 : ℝ) ^ 2) (Icc (-H) H)
      simpa only [one_pow] using hc)
  simp only [mul_one, one_pow, integral_const, measureReal_def,
    Measure.restrict_apply_univ, Real.volume_Icc,
    ENNReal.toReal_ofReal (by linarith only [hH] : 0 ≤ H - -H), smul_eq_mul,
    mul_one] at hcs
  have hb : (∫ u in Icc (-H) H, ‖f u‖ ^ 2) ≤ 1 := by
    rw [← hm]
    exact setIntegral_le_integral hs (Eventually.of_forall fun u => sq_nonneg _)
  have hmul := mul_le_mul_of_nonneg_right hb (by linarith only [hH] : 0 ≤ H - -H)
  nlinarith only [hcs, hmul]

/-- Physical first moment bounds the mass of a narrow Fourier window. -/
theorem fourierWindow_mass_le_firstMoment {f : ℝ → ℂ}
    (hf1 : Integrable f) (hf2 : MemLp f 2 volume)
    (hm : (∫ u, ‖f u‖ ^ 2) = 1)
    (hfirst : Integrable (fun u => |u| * ‖f u‖ ^ 2))
    {M : ℝ} (hM : (∫ u, |u| * ‖f u‖ ^ 2) ≤ M)
    {H η : ℝ} (hH : 0 < H) (hη : 0 ≤ η) :
    (∫ ξ in Icc (-η) η, ‖𝓕 f ξ‖ ^ 2) ≤ 8 * η * H + 2 * M / H := by
  let g : ℝ → ℂ := (Icc (-H) H).indicator f
  let r : ℝ → ℂ := fun u => f u - g u
  have hg1 : Integrable g := hf1.indicator measurableSet_Icc
  have hg2 : MemLp g 2 volume := hf2.indicator measurableSet_Icc
  have hr1 : Integrable r := hf1.sub hg1
  have hr2 : MemLp r 2 volume := hf2.sub hg2
  have hgr : (fun u => g u + r u) = f := by
    funext u
    dsimp only [r]
    ring
  have hgsq : (∫ u, ‖g u‖) ^ 2 ≤ 2 * H := by
    have heq : (fun u => ‖g u‖) = (Icc (-H) H).indicator (fun u => ‖f u‖) := by
      funext u
      by_cases hu : u ∈ Icc (-H) H
      · simp only [g, indicator_of_mem hu]
      · simp only [g, indicator_of_notMem hu, norm_zero]
    rw [heq, integral_indicator measurableSet_Icc]
    exact interval_norm_integral_sq_le hf1 hf2 hm hH
  have hrsq : Integrable (fun u => ‖r u‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm hr1.aestronglyMeasurable).mp hr2
  -- The first moment pays for the square mass outside the physical cutoff.
  have htail : (∫ u, ‖r u‖ ^ 2) ≤ M / H := by
    have hpt (u : ℝ) : H * ‖r u‖ ^ 2 ≤ |u| * ‖f u‖ ^ 2 := by
      by_cases hu : u ∈ Icc (-H) H
      · simp only [r, g, indicator_of_mem hu, sub_self, norm_zero,
          zero_pow two_ne_zero, mul_zero]
        exact mul_nonneg (abs_nonneg _) (sq_nonneg _)
      · have hle : H ≤ |u| := by
          by_contra hn
          have hh := abs_le.mp (le_of_lt (lt_of_not_ge hn))
          exact hu ⟨hh.1, hh.2⟩
        simp only [r, g, indicator_of_notMem hu, sub_zero]
        exact mul_le_mul_of_nonneg_right hle (sq_nonneg _)
    have hi := integral_mono (hrsq.const_mul H) hfirst hpt
    rw [integral_const_mul] at hi
    apply (le_div_iff₀ hH).mpr
    simpa only [mul_comm] using hi.trans hM
  -- The near part has bounded Fourier amplitude; Plancherel controls the far part.
  have hpoint (ξ : ℝ) : ‖𝓕 f ξ‖ ^ 2 ≤ 4 * H + 2 * ‖𝓕 r ξ‖ ^ 2 := by
    have he := fourierIntegral_add hg1 hr1 ξ
    rw [hgr] at he
    have hnorm : ‖𝓕 f ξ‖ ≤ ‖𝓕 g ξ‖ + ‖𝓕 r ξ‖ := by
      rw [he]
      exact norm_add_le _ _
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    have hg := (pow_le_pow_left₀ (norm_nonneg _) (norm_fourierIntegral_le_mass g ξ) 2).trans hgsq
    nlinarith only [hsq, hg, sq_nonneg (‖𝓕 g ξ‖ - ‖𝓕 r ξ‖)]
  have hri := RHTower.integrable_norm_sq_fourier hr1 hr2
  have hfi := RHTower.integrable_norm_sq_fourier hf1 hf2
  have hc : IntegrableOn (fun _ : ℝ => 4 * H) (Icc (-η) η) :=
    integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  have hi := integral_mono hfi.integrableOn (hc.add (hri.const_mul 2).integrableOn) hpoint
  change (∫ ξ in Icc (-η) η, ‖𝓕 f ξ‖ ^ 2) ≤
    ∫ ξ in Icc (-η) η, 4 * H + 2 * ‖𝓕 r ξ‖ ^ 2 at hi
  rw [integral_add hc (hri.const_mul 2).integrableOn,
    integral_const_mul (2 : ℝ) (fun ξ : ℝ => ‖𝓕 r ξ‖ ^ 2),
    integral_const, measureReal_def, Measure.restrict_apply_univ, Real.volume_Icc,
    ENNReal.toReal_ofReal (by linarith only [hη] : 0 ≤ η - -η), smul_eq_mul] at hi
  have hrf : (∫ ξ in Icc (-η) η, ‖𝓕 r ξ‖ ^ 2) ≤ M / H := by
    calc
      _ ≤ ∫ ξ, ‖𝓕 r ξ‖ ^ 2 :=
        setIntegral_le_integral hri (Eventually.of_forall fun ξ => sq_nonneg _)
      _ = ∫ u, ‖r u‖ ^ 2 := RHTower.integral_norm_sq_fourier_eq hr1 hr2
      _ ≤ _ := htail
  calc
    _ ≤ (η - -η) * (4 * H) + 2 * ∫ ξ in Icc (-η) η, ‖𝓕 r ξ‖ ^ 2 := hi
    _ ≤ (η - -η) * (4 * H) + 2 * (M / H) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hrf (by norm_num : (0 : ℝ) ≤ 2))
    _ = _ := by ring

/-- A bounded physical first moment excludes uniform concentration at frequency zero. -/
theorem exists_fourierWindow_small_of_firstMoment {M ε : ℝ}
    (hM : 0 ≤ M) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ {f : ℝ → ℂ}, Integrable f → MemLp f 2 volume →
      (∫ u, ‖f u‖ ^ 2) = 1 → Integrable (fun u => |u| * ‖f u‖ ^ 2) →
      (∫ u, |u| * ‖f u‖ ^ 2) ≤ M →
      ∀ {ζ : ℝ}, 0 ≤ ζ → ζ ≤ η → (∫ ξ in Icc (-ζ) ζ, ‖𝓕 f ξ‖ ^ 2) < ε := by
  let H : ℝ := (4 * M + 1) / ε
  have hH : 0 < H := div_pos (by positivity) hε
  have hHε : H * ε = 4 * M + 1 := div_mul_cancel₀ _ hε.ne'
  refine ⟨ε / (32 * H), by positivity, ?_⟩
  intro f hf1 hf2 hm hi hmf ζ hζ hζη
  have hb := fourierWindow_mass_le_firstMoment hf1 hf2 hm hi hmf hH hζ
  have hsmall : 8 * ζ * H ≤ ε / 4 := by
    have h := (le_div_iff₀ (by positivity : 0 < 32 * H)).mp hζη
    nlinarith only [h]
  have htail : 2 * M / H ≤ ε / 2 := by
    apply (div_le_iff₀ hH).mpr
    nlinarith only [hHε]
  linarith only [hb, hsmall, htail, hε]

#print axioms fourierWindow_mass_le_firstMoment
#print axioms exists_fourierWindow_small_of_firstMoment
end GaloisForLFunctions.HTGeometry
