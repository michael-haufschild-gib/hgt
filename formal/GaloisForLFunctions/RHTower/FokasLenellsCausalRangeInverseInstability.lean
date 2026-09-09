import GaloisForLFunctions.RHTower.FokasLenellsCausalImaginaryRange

/-! The unique actual inverse on each dense imaginary-axis range is algebraic and discontinuous.
Explicit right-hand sides tend to zero while their actual solutions keep unit data norm. -/
open Complex MeasureTheory Set Filter Topology
open scoped NNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

/-- The unique actual solution operator on the solvable imaginary-axis data, with no extension
outside the true range and no continuity built into its definition. -/
def causalImaginaryRangeInverse (ω : ℝ) :
    (causalComplexGeneratorShift ((ω : ℂ)*I)).range ≃ₗ[ℂ] causalGeneratorDomain :=
  (LinearEquiv.ofInjective (causalComplexGeneratorShift ((ω : ℂ)*I))
    (causalComplexGeneratorShift_imaginary_injective ω)).symm

/-- The actual range inverse solves every exactly solvable datum. -/
theorem causalImaginaryRangeInverse_equation (ω : ℝ)
    (y : (causalComplexGeneratorShift ((ω : ℂ)*I)).range) :
    causalComplexGeneratorShift ((ω : ℂ)*I) (causalImaginaryRangeInverse ω y) = y.val := by
  have h := (LinearEquiv.ofInjective (causalComplexGeneratorShift ((ω : ℂ)*I))
    (causalComplexGeneratorShift_imaginary_injective ω)).apply_symm_apply y
  exact congrArg (fun v : (causalComplexGeneratorShift ((ω : ℂ)*I)).range => v.val) h

/-- The range inverse returns the original actual maximal-domain solution. -/
theorem causalImaginaryRangeInverse_shift (ω : ℝ) (u : causalGeneratorDomain) :
    causalImaginaryRangeInverse ω
      ⟨causalComplexGeneratorShift ((ω : ℂ)*I) u, ⟨u, rfl⟩⟩ = u :=
  (LinearEquiv.ofInjective (causalComplexGeneratorShift ((ω : ℂ)*I))
    (causalComplexGeneratorShift_imaginary_injective ω)).symm_apply_apply u

/-- Explicit small exactly solvable data produced by the normalized rational boundary vectors. -/
def causalImaginaryBoundaryData (ω b : ℝ) :
    (causalComplexGeneratorShift ((ω : ℂ)*I)).range :=
  ⟨causalComplexGeneratorShift ((ω : ℂ)*I) (causalBoundaryEigenvector b ω),
    ⟨causalBoundaryEigenvector b ω, rfl⟩⟩

/-- The actual solvable boundary data have exact exponentially vanishing norms. -/
theorem norm_causalImaginaryBoundaryData (ω b : ℝ) :
    ‖causalImaginaryBoundaryData ω b‖ = Real.exp b :=
  norm_causalComplexGeneratorShift_boundaryEigenvector b ω

/-- The explicit exactly solvable data tend to zero in the actual range's inherited data topology. -/
theorem causalImaginaryBoundaryData_tendsto (ω : ℝ) :
    Tendsto (causalImaginaryBoundaryData ω) atBot (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.2
  simpa only [norm_causalImaginaryBoundaryData] using Real.tendsto_exp_atBot

/-- The unique actual solutions of those vanishing right-hand sides all have norm one. -/
theorem norm_causalImaginaryRangeInverse_boundaryData (ω b : ℝ) :
    ‖causalImaginaryRangeInverse ω (causalImaginaryBoundaryData ω b)‖ = 1 := by
  rw [causalImaginaryBoundaryData, causalImaginaryRangeInverse_shift, norm_causalBoundaryEigenvector]

/-- The actual unique inverse on each dense solvable imaginary-axis range is discontinuous. -/
theorem causalImaginaryRangeInverse_not_continuous (ω : ℝ) :
    ¬ Continuous (causalImaginaryRangeInverse ω) := by
  intro h
  have ht := (h.tendsto 0).comp (causalImaginaryBoundaryData_tendsto ω)
  have hn := ht.norm
  change Tendsto (fun b : ℝ => ‖causalImaginaryRangeInverse ω (causalImaginaryBoundaryData ω b)‖)
    atBot (𝓝 ‖causalImaginaryRangeInverse ω 0‖) at hn
  simp only [norm_causalImaginaryRangeInverse_boundaryData, map_zero, norm_zero] at hn
  have hbad : (1 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds hn
  exact one_ne_zero hbad

end
end RHTower.FokasLenells
