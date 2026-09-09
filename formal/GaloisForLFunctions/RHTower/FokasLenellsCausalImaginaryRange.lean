import GaloisForLFunctions.RHTower.FokasLenellsCausalGraphShift

/-! Dense but proper imaginary-axis ranges for the actual maximal causal generator.
Rational eigenvectors give density; Banach open mapping on the complete graph rules out surjectivity. -/
open Complex MeasureTheory Set Filter Topology
open scoped NNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section
local instance : CompleteSpace (hardyL2ᗮ) := hardyL2.isClosed_orthogonal.completeSpace_coe
local instance : CompleteSpace causalGeneratorGraph := isClosed_causalGeneratorGraph.completeSpace_coe

/-- Every rational Cauchy eigenvector lies in every actual imaginary-axis shift range. -/
theorem causalComplexGeneratorShift_imaginary_range_cauchyEigenvector (ω : ℝ)
    (w : {z : ℂ // 0 < z.im}) :
    causalCauchyEigenvector w ∈ (causalComplexGeneratorShift ((ω : ℂ)*I)).range := by
  have hm : ((ω : ℂ)*I).re = 0 := by simp
  have hne : (ω : ℂ)*I-causalPoleRate w.val ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    rw [Complex.sub_re, hm, Complex.zero_re] at hre
    have hw := causalPoleRate_re_neg w
    linarith only [hre, hw]
  refine ⟨((ω : ℂ)*I-causalPoleRate w.val)⁻¹ • causalCauchyEigenDomain w, ?_⟩
  rw [map_smul]
  change ((ω : ℂ)*I-causalPoleRate w.val)⁻¹ •
    (((ω : ℂ)*I) • (causalCauchyEigenDomain w).val -
      causalGenerator (causalCauchyEigenDomain w)) = causalCauchyEigenvector w
  rw [causalGenerator_cauchyEigenDomain, ← sub_smul, inv_smul_smul₀ hne]
  rfl

/-- Every actual imaginary-axis shifted equation has a dense set of exactly solvable right-hand sides. -/
theorem causalComplexGeneratorShift_imaginary_denseRange (ω : ℝ) :
    DenseRange (causalComplexGeneratorShift ((ω : ℂ)*I)) := by
  have hs : Submodule.span ℂ (Set.range causalCauchyEigenvector) ≤
      (causalComplexGeneratorShift ((ω : ℂ)*I)).range := by
    apply Submodule.span_le.mpr
    rintro u ⟨w, rfl⟩
    exact causalComplexGeneratorShift_imaginary_range_cauchyEigenvector ω w
  intro u
  have hu : u ∈ closure (Submodule.span ℂ (Set.range causalCauchyEigenvector) : Set (hardyL2ᗮ)) := by
    rw [← Submodule.topologicalClosure_coe, topologicalClosure_span_causalCauchyEigenvector_eq_top]
    trivial
  exact closure_mono hs hu

/-- No imaginary-axis shift admits any uniform inverse estimate in the original data norm. -/
theorem causalComplexGeneratorShift_imaginary_no_bound (ω : ℝ) :
    ¬ ∃ C : ℝ, ∀ u : causalGeneratorDomain,
      ‖u.val‖ ≤ C * ‖causalComplexGeneratorShift ((ω : ℂ)*I) u‖ := by
  rintro ⟨C, hC⟩
  have hb (b : ℝ) : 1 ≤ C * Real.exp b := by
    have h := hC (causalBoundaryEigenvector b ω)
    change ‖causalBoundaryEigenvector b ω‖ ≤
      C * ‖causalComplexGeneratorShift ((ω : ℂ)*I) (causalBoundaryEigenvector b ω)‖ at h
    rw [norm_causalBoundaryEigenvector, norm_causalComplexGeneratorShift_boundaryEigenvector] at h
    exact h
  have ht : Tendsto (fun b : ℝ => C*Real.exp b) atBot (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul Real.tendsto_exp_atBot
  have hbad : (1 : ℝ) ≤ 0 := ge_of_tendsto ht (Eventually.of_forall hb)
  linarith only [hbad]

/-- The actual imaginary-axis equation is not onto: Banach preimage bounds contradict its unit
approximate eigenvectors. The complete space used here is the closed graph, not the original domain. -/
theorem causalComplexGeneratorShift_imaginary_not_surjective (ω : ℝ) :
    ¬ Function.Surjective (causalComplexGeneratorShift ((ω : ℂ)*I)) := by
  intro hs
  have hg := (causalComplexGraphShift_surjective_iff ((ω : ℂ)*I)).2 hs
  obtain ⟨C, _, hC⟩ := ContinuousLinearMap.exists_preimage_norm_le
    (causalComplexGraphShift ((ω : ℂ)*I)) hg
  apply causalComplexGeneratorShift_imaginary_no_bound ω
  refine ⟨C, fun u => ?_⟩
  obtain ⟨p, hp, hpnorm⟩ := hC (causalComplexGeneratorShift ((ω : ℂ)*I) u)
  have hd : causalGeneratorGraphDomain p = u := by
    apply causalComplexGeneratorShift_imaginary_injective ω
    rw [causalComplexGraphShift_graphDomain, hp]
  have he : causalGeneratorGraphInput p = u.val :=
    congrArg (fun v : causalGeneratorDomain => v.val) hd
  calc ‖u.val‖ = ‖causalGeneratorGraphInput p‖ := congrArg norm he.symm
    _ ≤ ‖p‖ := causalGeneratorGraphInput_norm_le p
    _ ≤ C * ‖causalComplexGeneratorShift ((ω : ℂ)*I) u‖ := hpnorm

/-- Every imaginary-axis shift range is nonclosed despite its density in the actual data space. -/
theorem causalComplexGeneratorShift_imaginary_range_not_closed (ω : ℝ) :
    ¬ IsClosed (Set.range (causalComplexGeneratorShift ((ω : ℂ)*I))) := by
  intro hc
  apply causalComplexGeneratorShift_imaginary_not_surjective ω
  intro u
  have h : u ∈ closure (Set.range (causalComplexGeneratorShift ((ω : ℂ)*I))) :=
    causalComplexGeneratorShift_imaginary_denseRange ω u
  rw [hc.closure_eq] at h
  exact h

end
end RHTower.FokasLenells
