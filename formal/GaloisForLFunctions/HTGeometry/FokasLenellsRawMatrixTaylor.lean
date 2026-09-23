import GaloisForLFunctions.HTGeometry.FokasLenellsRawEndpointTaylor

/-!
# Matrix coefficients of the genuine cubic endpoint expansion

The actual vector expansions assemble into the determinant-one Jost
endpoint matrices. Their cubic matrix remainders converge at zero. In two
dimensions the adjugate is linear, so inversion preserves the exact finite
expansion without introducing a denominator or an invertibility premise.
-/

open Complex Matrix MeasureTheory Filter Topology
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

def rawQuadraticEndpointMatrix (q : SchwartzMap ℝ ℂ) (left : Bool) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(rawSecondEndpoint q 0 (1,0) left).1,(rawSecondEndpoint q 0 (0,1) left).1;
    (rawSecondEndpoint q 0 (1,0) left).2,(rawSecondEndpoint q 0 (0,1) left).2]

def rawCubicEndpointMatrix (q : SchwartzMap ℝ ℂ) (k : ℝ) (left : Bool) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(rawThirdEndpoint q k (1,0) left).1,(rawThirdEndpoint q k (0,1) left).1;
    (rawThirdEndpoint q k (1,0) left).2,(rawThirdEndpoint q k (0,1) left).2]

/-- The actual determinant-one endpoint matrix has an exact cubic expansion. -/
theorem rawAsymptoticMatrix_cubic_factor (q : SchwartzMap ℝ ℂ) (k : ℝ) (left : Bool) :
    rawAsymptoticMatrix q k left = 1+(k : ℂ) • rawFirstCoefficientMatrix q+
      (k : ℂ)^(2 : ℕ) • rawQuadraticEndpointMatrix q left+(k : ℂ)^(3 : ℕ) • rawCubicEndpointMatrix q k left := by
  have h1 := rawAsymptoticVector_third_factor q k (1,0) left
  have h2 := rawAsymptoticVector_third_factor q k (0,1) left
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [rawAsymptoticMatrix,rawFirstCoefficientMatrix,rawFirstCoefficient,
      rawQuadraticEndpointMatrix,rawCubicEndpointMatrix,Matrix.one_apply,smul_eq_mul] using congrArg Prod.fst h1
  · simpa [rawAsymptoticMatrix,rawFirstCoefficientMatrix,rawFirstCoefficient,
      rawQuadraticEndpointMatrix,rawCubicEndpointMatrix,Matrix.one_apply,smul_eq_mul] using congrArg Prod.fst h2
  · simpa [rawAsymptoticMatrix,rawFirstCoefficientMatrix,rawFirstCoefficient,
      rawQuadraticEndpointMatrix,rawCubicEndpointMatrix,Matrix.one_apply,smul_eq_mul] using congrArg Prod.snd h1
  · simpa [rawAsymptoticMatrix,rawFirstCoefficientMatrix,rawFirstCoefficient,
      rawQuadraticEndpointMatrix,rawCubicEndpointMatrix,Matrix.one_apply,smul_eq_mul] using congrArg Prod.snd h2

theorem rawCubicEndpointMatrix_tendsto_zero (q : SchwartzMap ℝ ℂ) (left : Bool) :
    Tendsto (fun k => rawCubicEndpointMatrix q k left) (𝓝 0) (𝓝 (rawCubicEndpointMatrix q 0 left)) := by
  have hc : Continuous (fun p : SpectralVector × SpectralVector =>
      (!![p.1.1,p.2.1;p.1.2,p.2.2] : Matrix (Fin 2) (Fin 2) ℂ)) := by fun_prop
  exact (hc.tendsto _).comp ((rawThirdEndpoint_tendsto_zero q (1,0) left).prodMk_nhds
    (rawThirdEndpoint_tendsto_zero q (0,1) left))

/-- Two-dimensional adjugation is additive, unlike adjugation in general dimension. -/
theorem rawAdjugate_add (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    (A+B).adjugate = A.adjugate+B.adjugate := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.adjugate_fin_two,add_comm]

theorem rawAdjugate_smul (c : ℂ) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    (c • A).adjugate = c • A.adjugate := by
  simpa using Matrix.adjugate_smul c A

theorem rawFirstCoefficientMatrix_adjugate (q : SchwartzMap ℝ ℂ) :
    (rawFirstCoefficientMatrix q).adjugate = -rawFirstCoefficientMatrix q := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rawFirstCoefficientMatrix,Matrix.adjugate_fin_two]

/-- The exact cubic inverse expansion uses only the already proved determinant-one law. -/
theorem rawAsymptoticMatrix_inverse_cubic_factor (q : SchwartzMap ℝ ℂ) (k : ℝ) (left : Bool) :
    (rawAsymptoticMatrix q k left)⁻¹ = 1-(k : ℂ) • rawFirstCoefficientMatrix q+
      (k : ℂ)^(2 : ℕ) • (rawQuadraticEndpointMatrix q left).adjugate+
      (k : ℂ)^(3 : ℕ) • (rawCubicEndpointMatrix q k left).adjugate := by
  rw [Matrix.inv_def,rawAsymptoticMatrix_det]
  simp only [Ring.inverse_one,one_smul]
  rw [rawAsymptoticMatrix_cubic_factor]
  simp only [rawAdjugate_add,rawAdjugate_smul,Matrix.adjugate_one,
    rawFirstCoefficientMatrix_adjugate,smul_neg,sub_eq_add_neg]

end
end GaloisForLFunctions.HTGeometry.FokasLenells
