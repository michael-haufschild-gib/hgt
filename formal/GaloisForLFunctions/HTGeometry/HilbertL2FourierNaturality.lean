import GaloisForLFunctions.HTGeometry.VectorL2FourierMultiplier

/-! Continuous Hilbert-space probes commute with the actual L² Fourier transform. -/
namespace GaloisForLFunctions.HTGeometry
open MeasureTheory FourierTransform
open scoped SchwartzMap
noncomputable section
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [CompleteSpace H] [CompleteSpace K] in
theorem compLp_schwartz_toLp (L : H →L[ℂ] K) (f : 𝓢(ℝ,H)) :
    L.compLp (f.toLp 2) = (f.postcompCLM L).toLp 2 := by
  apply Lp.ext
  filter_upwards [L.coeFn_compLp (f.toLp 2),f.coeFn_toLp 2,(f.postcompCLM L).coeFn_toLp 2]
    with x hL hf hg
  rw [hL,hf,hg,SchwartzMap.postcompCLM_apply]

theorem postcomp_schwartz_fourier (L : H →L[ℂ] K) (f : 𝓢(ℝ,H)) :
    (𝓕 f).postcompCLM L = 𝓕 (f.postcompCLM L) := by
  apply SchwartzMap.ext
  intro x
  change L ((𝓕 (f : ℝ → H)) x) = (𝓕 (fun y => L (f y))) x
  rw [Real.fourier_eq,Real.fourier_eq]
  have hi := (Real.fourierIntegral_convergent_iff (μ := (volume : Measure ℝ)) x).mpr
    (f.integrable (μ := volume))
  simpa only [Circle.smul_def,map_smul] using (L.integral_comp_comm hi).symm

/-- Naturality holds for every L² vector, after actual Schwartz density and continuous extension. -/
theorem compLp_fourier (L : H →L[ℂ] K) (f : Lp H 2 (volume : Measure ℝ)) :
    L.compLp (𝓕 f) = 𝓕 (L.compLp f) := by
  apply DenseRange.induction_on (p := fun f : Lp H 2 (volume : Measure ℝ) =>
    L.compLp (𝓕 f) = 𝓕 (L.compLp f))
    (SchwartzMap.denseRange_toLpCLM (p := 2) ENNReal.ofNat_ne_top) f
  · exact isClosed_eq
      ((L.compLpL 2 volume).continuous.comp (Lp.fourierTransformₗᵢ ℝ H).continuous)
      ((Lp.fourierTransformₗᵢ ℝ K).continuous.comp (L.compLpL 2 volume).continuous)
  intro g
  change L.compLp (𝓕 (g.toLp 2)) = 𝓕 (L.compLp (g.toLp 2))
  rw [SchwartzMap.toLp_fourier_eq,compLp_schwartz_toLp,compLp_schwartz_toLp,
    SchwartzMap.toLp_fourier_eq,postcomp_schwartz_fourier]

theorem compLp_fourierInv (L : H →L[ℂ] K) (f : Lp H 2 (volume : Measure ℝ)) :
    L.compLp (𝓕⁻ f) = 𝓕⁻ (L.compLp f) := by
  apply (Lp.fourierTransformₗᵢ ℝ K).injective
  change 𝓕 (L.compLp (𝓕⁻ f)) = 𝓕 (𝓕⁻ (L.compLp f))
  rw [← compLp_fourier,fourier_fourierInv_eq,fourier_fourierInv_eq]

end
end GaloisForLFunctions.HTGeometry
