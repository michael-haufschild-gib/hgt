import GaloisForLFunctions.HTGeometry.FokasLenellsRawSecondPrimitive

/-!
# Explicit second coefficients at both scattering infinities

The anchored mixed primitive has two actual endpoints. Decay of the Schwartz
profile evaluates the second Jost coefficients exactly in terms of those
endpoints. Their difference is the whole-line mixed integral.
-/

open Complex Matrix MeasureTheory Filter Topology
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

private theorem raw_oriented_primitive_tendsto {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (f : ℝ → E) (hf : Integrable f) (left : Bool) :
    Tendsto (fun x : ℝ => ∫ s in (0 : ℝ)..(if left then -x else x), f s) atTop
      (𝓝 (∫ s in Set.Ioi (0 : ℝ), if left then -f (-s) else f s)) := by
  cases left
  · exact intervalIntegral_tendsto_integral_Ioi 0 hf.integrableOn tendsto_id
  · have hh : Tendsto (fun x : ℝ => ∫ s in (0 : ℝ)..x, -f (-s)) atTop
        (𝓝 (∫ s in Set.Ioi (0 : ℝ), -f (-s))) :=
      intervalIntegral_tendsto_integral_Ioi 0 hf.comp_neg.neg.integrableOn tendsto_id
    have he (x : ℝ) : (∫ s in (0 : ℝ)..x, -f (-s)) = ∫ s in (0 : ℝ)..(-x), f s := by
      rw [intervalIntegral.integral_neg,intervalIntegral.integral_comp_neg,neg_zero,
        ← intervalIntegral.integral_symm]
    convert! hh using 1
    funext x
    exact (he x).symm

def rawMixedEndpoint (q : SchwartzMap ℝ ℂ) (left : Bool) : ℂ :=
  ∫ x in Set.Ioi (0 : ℝ), if left then -rawMixedProfile q (-x) else rawMixedProfile q x

def rawMixedTotal (q : SchwartzMap ℝ ℂ) : ℂ := ∫ x : ℝ, rawMixedProfile q x

theorem rawMixedPrimitive_tendsto (q : SchwartzMap ℝ ℂ) (left : Bool) :
    Tendsto (fun x : ℝ => rawMixedPrimitive q (if left then -x else x)) atTop (𝓝 (rawMixedEndpoint q left)) :=
  raw_oriented_primitive_tendsto (rawMixedProfile q) (rawMixedProfile q).integrable left

theorem rawSecondSlope_tendsto_endpoint (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) (left : Bool) :
    Tendsto (fun x : ℝ => rawSecondSlope q k v (if left then -x else x)) atTop (𝓝 (rawSecondEndpoint q k v left)) :=
  raw_oriented_primitive_tendsto (rawSecondIntegrand q k v) (rawSecondIntegrand_integrable q k v) left

theorem rawSecondPrimitive_tendsto (q : SchwartzMap ℝ ℂ) (v : SpectralVector) (left : Bool) :
    Tendsto (fun x : ℝ => rawSecondPrimitive q v (if left then -x else x)) atTop
      (𝓝 ((-rawMixedEndpoint q left-(q 0)^2)*v.1,rawMixedEndpoint q left*v.2)) := by
  have hJ := rawMixedPrimitive_tendsto q left
  have hq : Tendsto (fun x : ℝ => q (if left then -x else x)) atTop (𝓝 0) := by
    cases left
    · exact q.tendsto_cocompact.mono_left atTop_le_cocompact
    · exact (q.tendsto_cocompact.mono_left atBot_le_cocompact).comp tendsto_neg_atTop_atBot
  have hg : Tendsto (fun x : ℝ => q (-(if left then -x else x))) atTop (𝓝 0) := by
    cases left
    · exact (q.tendsto_cocompact.mono_left atBot_le_cocompact).comp tendsto_neg_atTop_atBot
    · simpa only [↓reduceIte,neg_neg] using (q.tendsto_cocompact.mono_left atTop_le_cocompact)
  have hc : Continuous (fun p : ℂ × (ℂ × ℂ) =>
      (((-p.1+q 0*p.2.2-(q 0)^2)*v.1,(p.1-p.2.1*p.2.2+q 0*p.2.1)*v.2) : SpectralVector)) := by fun_prop
  have hh := (hc.tendsto (rawMixedEndpoint q left,(0,0))).comp (hJ.prodMk_nhds (hq.prodMk_nhds hg))
  simpa only [Function.comp_def,rawSecondPrimitive,mul_zero,zero_mul,add_zero,sub_zero] using hh

/-- The actual quadratic endpoint coefficient is explicitly diagonal for arbitrary Schwartz profiles. -/
theorem rawSecondEndpoint_eq (q : SchwartzMap ℝ ℂ) (v : SpectralVector) (left : Bool) :
    rawSecondEndpoint q 0 v left =
      ((-rawMixedEndpoint q left-(q 0)^2)*v.1,rawMixedEndpoint q left*v.2) := by
  have hh := rawSecondSlope_tendsto_endpoint q 0 v left
  simp only [rawSecondSlope_zero_eq] at hh
  exact tendsto_nhds_unique hh (rawSecondPrimitive_tendsto q v left)

theorem rawQuadraticEndpointMatrix_eq (q : SchwartzMap ℝ ℂ) (left : Bool) :
    rawQuadraticEndpointMatrix q left =
      !![-rawMixedEndpoint q left-(q 0)^2,0;0,rawMixedEndpoint q left] := by
  simp only [rawQuadraticEndpointMatrix,rawSecondEndpoint_eq,mul_one,mul_zero]

/-- The difference of the actual oriented endpoints is the full mixed integral. -/
theorem rawMixedEndpoint_difference (q : SchwartzMap ℝ ℂ) :
    rawMixedEndpoint q false-rawMixedEndpoint q true = rawMixedTotal q := by
  have hh := intervalIntegral.integral_Iic_add_Ioi (μ := volume) (b := (0 : ℝ))
    (rawMixedProfile q).integrable.integrableOn (rawMixedProfile q).integrable.integrableOn
  unfold rawMixedEndpoint rawMixedTotal
  simp only [Bool.false_eq_true,↓reduceIte,integral_neg,integral_comp_neg_Ioi,neg_zero,sub_neg_eq_add]
  simpa only [add_comm] using hh

end
end GaloisForLFunctions.HTGeometry.FokasLenells
