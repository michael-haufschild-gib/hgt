import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ComplexCausalLaplaceMoments

/-!
# The complex resolvent moment law at neutral exponential decay

Negative-half-line support gives a common L¹ majorant for positive Laplace
weights. Continuity then joins the causal and anti-causal moment laws across
the vertical line where neither weighted kernel has exponential decay.
-/

noncomputable section
open MeasureTheory Filter Set Topology
open scoped Convolution

namespace GaloisForLFunctions.HTGeometry

/-- A vanishing Laplace coefficient removes the entire positive complex tail. -/
theorem complexCausalConvolution_support_of_laplace_zero {z : ℂ} {f : ℝ → ℂ}
    (hi : Integrable (complexLaplaceWeighted z f))
    (hz : negativeHalfLineLaplace f z = 0)
    (hs : ∀ u, 0 ≤ u → f u = 0) :
    ∀ y, 0 ≤ y → (complexRateCausalKernel z ⋆[ContinuousLinearMap.mul ℂ ℂ] f) y = 0 := by
  intro y hy
  have ht : (∫ u in Ioi y, Complex.exp (z * (u : ℂ)) * f u) = 0 := by
    rw [← integral_indicator measurableSet_Ioi]
    have he : (Ioi y).indicator (fun u => Complex.exp (z * (u : ℂ)) * f u) =
        fun _ => (0 : ℂ) := by
      funext u
      by_cases hu : u ∈ Ioi y
      · rw [indicator_of_mem hu, hs u (hy.trans (le_of_lt hu)), mul_zero]
      · rw [indicator_of_notMem hu]
    rw [he, integral_zero]
  rw [complexCausalConvolution_eq_upper_laplace_of_zero hi hz, ht, mul_zero]

/-- Continuity supplies the resolvent identity on the neutral vertical line. -/
theorem negativeHalfLineLaplace_causalConvolution_mul_of_re_eq {z q : ℂ}
    (hzpos : 0 < z.re) (heq : q.re = z.re) {f : ℝ → ℂ}
    (hf : Integrable f) (hs : ∀ u, 0 ≤ u → f u = 0)
    (hz : negativeHalfLineLaplace f z = 0) :
    (z - q) * negativeHalfLineLaplace
      (complexRateCausalKernel z ⋆[ContinuousLinearMap.mul ℂ ℂ] f) q =
      (Real.pi : ℂ) * negativeHalfLineLaplace f q := by
  let K := complexRateCausalKernel z ⋆[ContinuousLinearMap.mul ℂ ℂ] f
  have hi : Integrable (complexLaplaceWeighted z f) :=
    integrable_negativeHalfLineLaplace hf hs hzpos.le
  have hK : Integrable K :=
    (integrable_complexRateCausalKernel hzpos).integrable_convolution
      (ContinuousLinearMap.mul ℂ ℂ) hf
  have hKs : ∀ u, 0 ≤ u → K u = 0 :=
    complexCausalConvolution_support_of_laplace_zero hi hz hs
  have hq : 0 ≤ q.re := by rw [heq]; exact hzpos.le
  let qs : ℕ → ℂ := fun n => q + (((n + 1 : ℕ) : ℝ)⁻¹ : ℂ)
  have hseq : Tendsto qs atTop (𝓝 q) := by
    have hr : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)⁻¹) atTop (𝓝 0) :=
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)).inv_tendsto_atTop
    have hc := Filter.Tendsto.comp (Complex.continuous_ofReal.tendsto 0) hr
    simpa only [Complex.ofReal_zero, add_zero] using
      (tendsto_const_nhds (x := q)).add hc
  have hpos (n : ℕ) : 0 < ((n + 1 : ℕ) : ℝ)⁻¹ := by positivity
  have hqs (n : ℕ) : 0 ≤ (qs n).re := by
    change 0 ≤ (q + (((n + 1 : ℕ) : ℝ)⁻¹ : ℂ)).re
    simpa only [Complex.add_re, Complex.ofReal_re] using add_nonneg hq (hpos n).le
  have hwithin : Tendsto qs atTop (𝓝[{w : ℂ | 0 ≤ w.re}] q) :=
    tendsto_nhdsWithin_iff.mpr ⟨hseq, Eventually.of_forall hqs⟩
  have hleft : Tendsto (fun n => (z - qs n) * negativeHalfLineLaplace K (qs n))
      atTop (𝓝 ((z - q) * negativeHalfLineLaplace K q)) :=
    (tendsto_const_nhds.sub hseq).mul
      (Filter.Tendsto.comp (continuousOn_negativeHalfLineLaplace hK hKs q hq) hwithin)
  have hright : Tendsto (fun n => (Real.pi : ℂ) * negativeHalfLineLaplace f (qs n))
      atTop (𝓝 ((Real.pi : ℂ) * negativeHalfLineLaplace f q)) :=
    tendsto_const_nhds.mul
      (Filter.Tendsto.comp (continuousOn_negativeHalfLineLaplace hf hs q hq) hwithin)
  have hidentity (n : ℕ) :
      (z - qs n) * negativeHalfLineLaplace K (qs n) =
        (Real.pi : ℂ) * negativeHalfLineLaplace f (qs n) := by
    have hd : 0 < (qs n - z).re := by
      change 0 < (q + (((n + 1 : ℕ) : ℝ)⁻¹ : ℂ) - z).re
      simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, heq]
      linarith only [hpos n]
    have hn : z - qs n ≠ 0 := by
      intro h
      have hr := congrArg Complex.re h
      simp only [Complex.sub_re, Complex.zero_re] at hr
      simp only [Complex.sub_re] at hd
      linarith only [hr, hd]
    rw [negativeHalfLineLaplace_causalConvolution_of_gt hd hi hz
      (integrable_negativeHalfLineLaplace hf hs (hqs n))]
    field_simp [hn]
  exact tendsto_nhds_unique hleft
    (hright.congr' (Eventually.of_forall fun n => (hidentity n).symm))

/-- The exact complex resolvent law holds at every admitted Laplace argument. -/
theorem negativeHalfLineLaplace_causalConvolution_mul {z q : ℂ} (hzpos : 0 < z.re)
    {f : ℝ → ℂ} (hf : Integrable f) (hs : ∀ u, 0 ≤ u → f u = 0)
    (hz : negativeHalfLineLaplace f z = 0)
    (hq : Integrable (complexLaplaceWeighted q f)) :
    (z - q) * negativeHalfLineLaplace
      (complexRateCausalKernel z ⋆[ContinuousLinearMap.mul ℂ ℂ] f) q =
      (Real.pi : ℂ) * negativeHalfLineLaplace f q := by
  rcases lt_trichotomy q.re z.re with hlt | heq | hgt
  · have hd : 0 < (z - q).re := by
      simpa only [Complex.sub_re] using sub_pos.mpr hlt
    have hn : z - q ≠ 0 := by
      intro h
      rw [h, Complex.zero_re] at hd
      exact (lt_irrefl 0) hd
    rw [negativeHalfLineLaplace_causalConvolution_of_lt hd hq]
    field_simp [hn]
  · exact negativeHalfLineLaplace_causalConvolution_mul_of_re_eq hzpos heq hf hs hz
  · have hd : 0 < (q - z).re := by
      simpa only [Complex.sub_re] using sub_pos.mpr hgt
    have hn : z - q ≠ 0 := by
      intro h
      have hr := congrArg Complex.re h
      simp only [Complex.sub_re, Complex.zero_re] at hr
      linarith only [hgt, hr]
    rw [negativeHalfLineLaplace_causalConvolution_of_gt hd
      (integrable_negativeHalfLineLaplace hf hs hzpos.le) hz hq]
    field_simp [hn]

end GaloisForLFunctions.HTGeometry
