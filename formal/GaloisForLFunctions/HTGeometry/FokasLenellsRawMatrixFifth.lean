import GaloisForLFunctions.HTGeometry.FokasLenellsRawEndpointFifth

/-!
# Exact fifth-order Jost matrix and inverse expansions

The true vector coefficients assemble into matrix coefficients. The proven
determinant-one identity makes the two-dimensional inverse expansion exact.
-/

open Complex Matrix MeasureTheory Filter Topology
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

def rawQuarticEndpointMatrix (q : SchwartzMap ℝ ℂ) (left : Bool) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(rawFourthEndpoint q 0 (1,0) left).1,(rawFourthEndpoint q 0 (0,1) left).1;
    (rawFourthEndpoint q 0 (1,0) left).2,(rawFourthEndpoint q 0 (0,1) left).2]

def rawQuinticEndpointMatrix (q : SchwartzMap ℝ ℂ) (k : ℝ) (left : Bool) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(rawFifthEndpoint q k (1,0) left).1,(rawFifthEndpoint q k (0,1) left).1;
    (rawFifthEndpoint q k (1,0) left).2,(rawFifthEndpoint q k (0,1) left).2]

theorem rawCubicEndpointMatrix_fifth_factor (q : SchwartzMap ℝ ℂ) (k : ℝ) (left : Bool) :
    rawCubicEndpointMatrix q k left = rawCubicEndpointMatrix q 0 left+
      (k : ℂ) • rawQuarticEndpointMatrix q left+(k : ℂ)^2 • rawQuinticEndpointMatrix q k left := by
  have h (v : SpectralVector) : rawThirdEndpoint q k v left = rawThirdEndpoint q 0 v left+
      (k : ℂ) • rawFourthEndpoint q 0 v left+(k : ℂ)^2 • rawFifthEndpoint q k v left := by
    rw [rawThirdEndpoint_fourth_factor,rawFourthEndpoint_fifth_factor]
    module
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [rawCubicEndpointMatrix,rawQuarticEndpointMatrix,rawQuinticEndpointMatrix,smul_eq_mul] using congrArg Prod.fst (h (1,0))
  · simpa [rawCubicEndpointMatrix,rawQuarticEndpointMatrix,rawQuinticEndpointMatrix,smul_eq_mul] using congrArg Prod.fst (h (0,1))
  · simpa [rawCubicEndpointMatrix,rawQuarticEndpointMatrix,rawQuinticEndpointMatrix,smul_eq_mul] using congrArg Prod.snd (h (1,0))
  · simpa [rawCubicEndpointMatrix,rawQuarticEndpointMatrix,rawQuinticEndpointMatrix,smul_eq_mul] using congrArg Prod.snd (h (0,1))

/-- All five orders belong to the actual infinite endpoint matrix. -/
theorem rawAsymptoticMatrix_fifth_factor (q : SchwartzMap ℝ ℂ) (k : ℝ) (left : Bool) :
    rawAsymptoticMatrix q k left = 1+(k : ℂ) • rawFirstCoefficientMatrix q+
      (k : ℂ)^2 • rawQuadraticEndpointMatrix q left+(k : ℂ)^3 • rawCubicEndpointMatrix q 0 left+
      (k : ℂ)^4 • rawQuarticEndpointMatrix q left+(k : ℂ)^5 • rawQuinticEndpointMatrix q k left := by
  rw [rawAsymptoticMatrix_cubic_factor,rawCubicEndpointMatrix_fifth_factor]
  module

theorem rawQuinticEndpointMatrix_tendsto_zero (q : SchwartzMap ℝ ℂ) (left : Bool) :
    Tendsto (fun k => rawQuinticEndpointMatrix q k left) (𝓝 0) (𝓝 (rawQuinticEndpointMatrix q 0 left)) := by
  have hc : Continuous (fun p : SpectralVector × SpectralVector =>
      (!![p.1.1,p.2.1;p.1.2,p.2.2] : Matrix (Fin 2) (Fin 2) ℂ)) := by fun_prop
  exact (hc.tendsto _).comp ((rawFifthEndpoint_tendsto_zero q (1,0) left).prodMk_nhds
    (rawFifthEndpoint_tendsto_zero q (0,1) left))

/-- No inverse regularity premise is needed: determinant one and the linear adjugate suffice. -/
theorem rawAsymptoticMatrix_inverse_fifth_factor (q : SchwartzMap ℝ ℂ) (k : ℝ) (left : Bool) :
    (rawAsymptoticMatrix q k left)⁻¹ = 1-(k : ℂ) • rawFirstCoefficientMatrix q+
      (k : ℂ)^2 • (rawQuadraticEndpointMatrix q left).adjugate+
      (k : ℂ)^3 • (rawCubicEndpointMatrix q 0 left).adjugate+
      (k : ℂ)^4 • (rawQuarticEndpointMatrix q left).adjugate+
      (k : ℂ)^5 • (rawQuinticEndpointMatrix q k left).adjugate := by
  rw [Matrix.inv_def,rawAsymptoticMatrix_det]
  simp only [Ring.inverse_one,one_smul]
  rw [rawAsymptoticMatrix_fifth_factor]
  simp only [rawAdjugate_add,rawAdjugate_smul,Matrix.adjugate_one,
    rawFirstCoefficientMatrix_adjugate,smul_neg,sub_eq_add_neg]

end
end GaloisForLFunctions.HTGeometry.FokasLenells
