import GaloisForLFunctions.HTGeometry.FokasLenellsContourJost
import GaloisForLFunctions.HTGeometry.FokasLenellsGaugeScattering

/-!
# The actual original fundamental matrix on all four contour rays

Pauli transport is identified with the independently constructed original
spatial evolution by its proved uniqueness theorem. This supplies the
missing bridge needed to compare signed-z uniformized scattering with
the contour-defined scattering matrix.
-/

open Complex Matrix Filter Topology
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

/-- Constant Pauli transport of the constructed positive-ray spatial fundamental matrix. -/
def contourFundamentalMatrix (q : SchwartzMap ℝ ℂ) (vertical negative : Bool) (κ x : ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  contourConjugator vertical negative * spatialFundamentalMatrix (contourSource q vertical) (κ : ℂ) x *
    contourConjugator vertical negative

/-- Every transported column solves the actual original spatial equation at its contour parameter. -/
theorem contourFundamentalMatrix_entry_hasDerivAt (q : SchwartzMap ℝ ℂ) (vertical negative : Bool)
    (κ x : ℝ) (i j : Fin 2) :
    HasDerivAt (fun y => contourFundamentalMatrix q vertical negative κ y i j)
      ((spatialLax (deriv q x) (reflectedDerivative q x) (contourParameter vertical negative κ) *
        contourFundamentalMatrix q vertical negative κ x) i j) x := by
  have hh := spatialDoubleCombination_entry_hasDerivAt (contourSource q vertical) (κ : ℂ)
    (contourConjugator vertical negative) (contourConjugator vertical negative) x i j
  simp only [← Matrix.mul_assoc] at hh
  refine hh.congr_deriv ?_
  rw [spatialLax_contour_conjugation]
  simp only [contourFundamentalMatrix, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (contourConjugator vertical negative) (contourConjugator vertical negative),
    contourConjugator_square, one_mul]

/-- Transport preserves the identity initial matrix. -/
theorem contourFundamentalMatrix_zero (q : SchwartzMap ℝ ℂ) (vertical negative : Bool) (κ : ℝ) :
    contourFundamentalMatrix q vertical negative κ 0 = 1 := by
  have hz : spatialFundamentalMatrix (contourSource q vertical) (κ : ℂ) 0 = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [spatialFundamentalMatrix, spatialEigenfunction_initial]
  rw [contourFundamentalMatrix, hz, mul_one, contourConjugator_square]

private theorem contour_fundamental_column_solution (q : SchwartzMap ℝ ℂ) (vertical negative : Bool)
    (κ : ℝ) (j : Fin 2) :
    IsSpatialSolution q (Complex.log (contourParameter vertical negative κ))
      ((1 : Matrix (Fin 2) (Fin 2) ℂ) 0 j, (1 : Matrix (Fin 2) (Fin 2) ℂ) 1 j)
      (fun x => (contourFundamentalMatrix q vertical negative κ x 0 j,
        contourFundamentalMatrix q vertical negative κ x 1 j)) := by
  constructor
  · change (contourFundamentalMatrix q vertical negative κ 0 0 j,
      contourFundamentalMatrix q vertical negative κ 0 1 j) = _
    rw [contourFundamentalMatrix_zero]
  · intro x
    have hh := (contourFundamentalMatrix_entry_hasDerivAt q vertical negative κ x 0 j).prodMk
      (contourFundamentalMatrix_entry_hasDerivAt q vertical negative κ x 1 j)
    refine hh.congr_deriv ?_
    rw [spatialOperator_eq_matrix, Complex.exp_log (contourParameter_ne_zero vertical negative κ)]
    simp only [reflectedDerivative_apply, matrixVector, Matrix.mulVec, dotProduct,
      Matrix.mul_apply, Fin.sum_univ_two]
    rfl

/-- Proved spatial uniqueness identifies Pauli transport with the actual independently constructed evolution. -/
theorem contourFundamentalMatrix_eq_spatial (q : SchwartzMap ℝ ℂ) (vertical negative : Bool) (κ x : ℝ) :
    contourFundamentalMatrix q vertical negative κ x =
      spatialFundamentalMatrix q (Complex.log (contourParameter vertical negative κ)) x := by
  have h0 := (spatialSolution_existsUnique q (Complex.log (contourParameter vertical negative κ)) (1,0)).unique
    (by simpa using contour_fundamental_column_solution q vertical negative κ 0)
    (spatialEigenfunction_isSpatialSolution q _ (1,0))
  have h1 := (spatialSolution_existsUnique q (Complex.log (contourParameter vertical negative κ)) (0,1)).unique
    (by simpa using contour_fundamental_column_solution q vertical negative κ 1)
    (spatialEigenfunction_isSpatialSolution q _ (0,1))
  ext i j
  fin_cases i <;> fin_cases j
  · exact congrArg Prod.fst (congrFun h0 x)
  · exact congrArg Prod.fst (congrFun h1 x)
  · exact congrArg Prod.snd (congrFun h0 x)
  · exact congrArg Prod.snd (congrFun h1 x)

/-- The exact uniformizing gauge holds on all four contour rays, including both imaginary rays. -/
theorem uniformizedFundamentalMatrix_contour_gauge (q : SchwartzMap ℝ ℂ) (vertical negative : Bool)
    (κ x : ℝ) :
    uniformizedFundamentalMatrix (SchwartzMap.derivCLM ℂ ℂ q) (reflectedDerivative q)
      (SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ q))
        (contourSquaredParameter vertical κ : ℂ) x *
      uniformizationGauge (deriv q 0) (contourParameter vertical negative κ) =
    uniformizationGauge (deriv q x) (contourParameter vertical negative κ) *
      contourFundamentalMatrix q vertical negative κ x := by
  have hh := uniformizedFundamentalMatrix_gauge q (Complex.log (contourParameter vertical negative κ)) x
  rwa [Complex.exp_log (contourParameter_ne_zero vertical negative κ), contourParameter_square,
    ← contourFundamentalMatrix_eq_spatial] at hh

end
end GaloisForLFunctions.HTGeometry.FokasLenells
