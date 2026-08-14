import GaloisForLFunctions.RHTower.MobiusLaplaceMellinPlancherelBridge

/-!
# Polarized Mellin--Plancherel line identity

The unitary `L²` Fourier transform preserves the Hermitian pairing, so two functions whose
logarithmic Mellin sources lie in `L¹ ∩ L²` satisfy

```text
∫_ℝ conj(M f(σ+it)) · M g(σ+it) dt = 2π · M (conj f · g)(2σ).
```

This is the polarized companion of the diagonal line law and is the exact form in which a
four-field parity determinant is transported between the physical half-line and the spectral
line.
-/

open Complex MeasureTheory Real Set Filter
open scoped FourierTransform ENNReal Topology

noncomputable section

namespace RHTower

/-- **Fourier polarization.**  The classical Fourier integral preserves the Hermitian pairing of
two `L¹ ∩ L²` functions. -/
theorem integral_conj_fourier_mul_fourier
    {F G : ℝ → ℂ} (hF1 : Integrable F) (hF2 : MemLp F 2 volume)
    (hG1 : Integrable G) (hG2 : MemLp G 2 volume) :
    (∫ ξ : ℝ, (starRingEnd ℂ) (𝓕 F ξ) * 𝓕 G ξ) =
      ∫ u : ℝ, (starRingEnd ℂ) (F u) * G u := by
  let F2 : Lp ℂ 2 (volume : Measure ℝ) := hF2.toLp F
  let G2 : Lp ℂ 2 (volume : Measure ℝ) := hG2.toLp G
  have hFcoe : (F2 : ℝ → ℂ) =ᵐ[volume] F := hF2.coeFn_toLp
  have hGcoe : (G2 : ℝ → ℂ) =ᵐ[volume] G := hG2.coeFn_toLp
  have hFint : Integrable (F2 : ℝ → ℂ) := hF1.congr hFcoe.symm
  have hGint : Integrable (G2 : ℝ → ℂ) := hG1.congr hGcoe.symm
  have hFfour : ((𝓕 F2 : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume] 𝓕 F := by
    calc ((𝓕 F2 : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume]
        (Real.Lp.fourierTransform
          ((memLp_one_iff_integrable.mpr hFint).toLp F2) : ℝ → ℂ) :=
          l2_fourier_coeFn_eq_l1_fourier_of_integrable F2 hFint
      _ =ᵐ[volume] 𝓕 F := Filter.Eventually.of_forall fun x => by
          rw [Real.fourierTransform_toLp]
          exact Real.fourier_congr_ae hFcoe x
  have hGfour : ((𝓕 G2 : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume] 𝓕 G := by
    calc ((𝓕 G2 : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume]
        (Real.Lp.fourierTransform
          ((memLp_one_iff_integrable.mpr hGint).toLp G2) : ℝ → ℂ) :=
          l2_fourier_coeFn_eq_l1_fourier_of_integrable G2 hGint
      _ =ᵐ[volume] 𝓕 G := Filter.Eventually.of_forall fun x => by
          rw [Real.fourierTransform_toLp]
          exact Real.fourier_congr_ae hGcoe x
  have hinner := MeasureTheory.Lp.inner_fourier_eq F2 G2
  rw [L2.inner_def, L2.inner_def] at hinner
  have hleft : (∫ ξ : ℝ, (starRingEnd ℂ) (𝓕 F ξ) * 𝓕 G ξ)
      = ∫ a : ℝ, (inner ℂ ((𝓕 F2 : Lp ℂ 2 (volume : Measure ℝ)) a)
          ((𝓕 G2 : Lp ℂ 2 (volume : Measure ℝ)) a) : ℂ) := by
    refine (integral_congr_ae ?_).symm
    filter_upwards [hFfour, hGfour] with a ha hb
    rw [RCLike.inner_apply', ha, hb]
  have hright : (∫ u : ℝ, (starRingEnd ℂ) (F u) * G u)
      = ∫ a : ℝ, (inner ℂ ((F2 : ℝ → ℂ) a) ((G2 : ℝ → ℂ) a) : ℂ) := by
    refine (integral_congr_ae ?_).symm
    filter_upwards [hFcoe, hGcoe] with a ha hb
    rw [RCLike.inner_apply', ha, hb]
  rw [hleft, hright, hinner]

/-- **Polarized Mellin line law.**  Two logarithmic sources in `L¹ ∩ L²` pair on the vertical line
exactly as their physical fields pair on the half-line. -/
theorem integral_conj_mellin_line_mul_mellin_line
    {f g : ℝ → ℂ} {sigma : ℝ}
    (hf1 : Integrable (logMellinLineSource f sigma))
    (hf2 : MemLp (logMellinLineSource f sigma) 2 volume)
    (hg1 : Integrable (logMellinLineSource g sigma))
    (hg2 : MemLp (logMellinLineSource g sigma) 2 volume) :
    (∫ t : ℝ, (starRingEnd ℂ) (mellin f ((sigma : ℂ) + (t : ℂ) * I)) *
        mellin g ((sigma : ℂ) + (t : ℂ) * I))
      = 2 * Real.pi * mellin (fun x : ℝ => (starRingEnd ℂ) (f x) * g x) ((2 * sigma : ℝ) : ℂ) := by
  set F : ℝ → ℂ := logMellinLineSource f sigma with hFdef
  set G : ℝ → ℂ := logMellinLineSource g sigma with hGdef
  -- the vertical integral is a rescaled Fourier pairing
  have hline : (fun t : ℝ => (starRingEnd ℂ) (mellin f ((sigma : ℂ) + (t : ℂ) * I)) *
      mellin g ((sigma : ℂ) + (t : ℂ) * I))
      = fun t : ℝ => ((fun ξ : ℝ => (starRingEnd ℂ) (𝓕 F ξ) * 𝓕 G ξ) (t / (2 * Real.pi))) := by
    funext t
    rw [mellin_line_eq_fourier_logMellinLineSource, mellin_line_eq_fourier_logMellinLineSource]
  rw [hline]
  have hscale := MeasureTheory.Measure.integral_comp_div
    (fun ξ : ℝ => (starRingEnd ℂ) (𝓕 F ξ) * 𝓕 G ξ) (2 * Real.pi)
  rw [hscale, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi),
    integral_conj_fourier_mul_fourier hf1 hf2 hg1 hg2]
  -- the physical pairing is the doubled Mellin transform
  have hphys : (∫ u : ℝ, (starRingEnd ℂ) (F u) * G u)
      = mellin (fun x : ℝ => (starRingEnd ℂ) (f x) * g x) ((2 * sigma : ℝ) : ℂ) := by
    rw [mellin_eq_integral_exp_neg_mul_log]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    have hexp : Complex.exp (-((2 * sigma : ℝ) : ℂ) * (u : ℂ))
        = ((Real.exp (-sigma * u) : ℝ) : ℂ) * ((Real.exp (-sigma * u) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, ← Real.exp_add, Complex.ofReal_exp]
      congr 1
      push_cast
      ring
    simp only [hFdef, hGdef, logMellinLineSource, Complex.real_smul, map_mul,
      Complex.conj_ofReal]
    rw [hexp]
    ring
  rw [hphys, Complex.real_smul]
  push_cast
  ring
end RHTower
