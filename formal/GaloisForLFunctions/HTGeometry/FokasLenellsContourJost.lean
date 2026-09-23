import GaloisForLFunctions.HTGeometry.FokasLenellsContourSymmetry

/-!
# Classical Jost bases on the full Fokas–Lenells contour

Pauli transport extends the constructed positive-real Jost bases to all four
nonzero rays of `Im(k²) = 0` in arXiv:2607.19649v1. Both endpoint
normalizations, determinant one, the original spatial equation (1.8), and
the normalized commutator equation (2.2) hold for every Schwartz potential.
The bases are constructed, and no differential-equation or endpoint
hypothesis is assumed.
-/

open Complex Matrix Filter
open scoped Topology Matrix.Norms.Elementwise
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

/-- The Boolean endpoint uses right normalization for `false` and left normalization for `true`. -/
def baseJostMatrix (q : SchwartzMap ℝ ℂ) (κ : ℝ) (left : Bool) (x : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  if left then leftJostMatrix q κ x else rightJostMatrix q κ x

def baseJostFunction (q : SchwartzMap ℝ ℂ) (κ : ℝ) (left : Bool) (x : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  if left then leftJostFunction q κ x else rightJostFunction q κ x

theorem baseJostMatrix_det (q : SchwartzMap ℝ ℂ) (κ : ℝ) (left : Bool) (x : ℝ) :
    (baseJostMatrix q κ left x).det = 1 := by
  cases left
  · exact rightJostMatrix_det q κ x
  · exact leftJostMatrix_det q κ x

theorem baseJostFunction_eq (q : SchwartzMap ℝ ℂ) (κ : ℝ) (left : Bool) (x : ℝ) :
    baseJostFunction q κ left x = baseJostMatrix q κ left x*diagonalFrame ((Real.exp κ)^(2 : ℕ)) x := by
  cases left <;> rfl

theorem baseJostFunction_tendsto (q : SchwartzMap ℝ ℂ) (κ : ℝ) (left : Bool) :
    Tendsto (fun x => baseJostFunction q κ left (if left then -x else x)) atTop (𝓝 1) := by
  cases left
  · exact rightJostFunction_tendsto_one q κ
  · exact (leftJostFunction_tendsto_one q κ).comp tendsto_neg_atTop_atBot

/-- Classical derivatives of constant double combinations of the constructed spatial basis. -/
theorem spatialDoubleCombination_entry_hasDerivAt (q : SchwartzMap ℝ ℂ) (a : ℂ)
    (P C : Matrix (Fin 2) (Fin 2) ℂ) (x : ℝ) (i j : Fin 2) :
    HasDerivAt (fun y => (P*(spatialFundamentalMatrix q a y*C)) i j)
      ((P*(spatialLax (deriv q x) (reflectedDerivative q x) (Complex.exp a)*
        (spatialFundamentalMatrix q a x*C))) i j) x := by
  have hd := ((spatialMatrixCombination_entry_hasDerivAt q a C x 0 j).const_mul (P i 0)).fun_add
    ((spatialMatrixCombination_entry_hasDerivAt q a C x 1 j).const_mul (P i 1))
  simpa only [reflectedDerivative_apply, Matrix.mul_apply, Fin.sum_univ_two] using hd

/-- Constant Pauli transport is differentiated before imposing the ray covariance. -/
theorem baseJostMatrix_conjugation_hasDerivAt (q : SchwartzMap ℝ ℂ) (κ : ℝ) (left : Bool)
    (P : Matrix (Fin 2) (Fin 2) ℂ) (x : ℝ) (i j : Fin 2) :
    HasDerivAt (fun y => (P*baseJostMatrix q κ left y*P) i j)
      ((P*(spatialLax (deriv q x) (reflectedDerivative q x) (Complex.exp (κ:ℂ))*
        baseJostMatrix q κ left x)*P) i j) x := by
  cases left
  · simpa only [baseJostMatrix, Bool.false_eq_true, ↓reduceIte, rightJostMatrix, Matrix.mul_assoc] using
      spatialDoubleCombination_entry_hasDerivAt q (κ:ℂ) P ((rightAsymptoticMatrix q κ)⁻¹*P) x i j
  · simpa only [baseJostMatrix, ↓reduceIte, leftJostMatrix, Matrix.mul_assoc] using
      spatialDoubleCombination_entry_hasDerivAt q (κ:ℂ) P ((leftAsymptoticMatrix q κ)⁻¹*P) x i j

def contourJostMatrix (q : SchwartzMap ℝ ℂ) (vertical negative : Bool) (κ : ℝ)
    (left : Bool) (x : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  contourConjugator vertical negative*baseJostMatrix (contourSource q vertical) κ left x*
    contourConjugator vertical negative

/-- Both Jost bases solve the original spatial equation on each of the four rays. -/
theorem contourJostMatrix_entry_hasDerivAt (q : SchwartzMap ℝ ℂ) (vertical negative : Bool)
    (κ : ℝ) (left : Bool) (x : ℝ) (i j : Fin 2) :
    HasDerivAt (fun y => contourJostMatrix q vertical negative κ left y i j)
      ((spatialLax (deriv q x) (reflectedDerivative q x) (contourParameter vertical negative κ)*
        contourJostMatrix q vertical negative κ left x) i j) x := by
  refine (baseJostMatrix_conjugation_hasDerivAt (contourSource q vertical) κ left
    (contourConjugator vertical negative) x i j).congr_deriv ?_
  rw [spatialLax_contour_conjugation]
  simp only [contourJostMatrix, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (contourConjugator vertical negative) (contourConjugator vertical negative),
    contourConjugator_square, one_mul]

theorem contourJostMatrix_det (q : SchwartzMap ℝ ℂ) (vertical negative : Bool)
    (κ : ℝ) (left : Bool) (x : ℝ) :
    (contourJostMatrix q vertical negative κ left x).det = 1 := by
  rw [contourJostMatrix, Matrix.det_mul, Matrix.det_mul, baseJostMatrix_det, mul_one]
  have hd := congrArg Matrix.det (contourConjugator_square vertical negative)
  simpa only [Matrix.det_mul, Matrix.det_one] using hd

def contourJostFunction (q : SchwartzMap ℝ ℂ) (vertical negative : Bool) (κ : ℝ)
    (left : Bool) (x : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  contourJostMatrix q vertical negative κ left x*diagonalFrame (contourSquaredParameter vertical κ) x

theorem contourJostFunction_conjugation (q : SchwartzMap ℝ ℂ) (vertical negative : Bool)
    (κ : ℝ) (left : Bool) (x : ℝ) :
    contourJostFunction q vertical negative κ left x =
      contourConjugator vertical negative*baseJostFunction (contourSource q vertical) κ left x*
        contourConjugator vertical negative := by
  unfold contourJostFunction
  rw [diagonalFrame_contour_conjugation vertical negative κ x]
  simp only [contourJostMatrix, baseJostFunction_eq, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (contourConjugator vertical negative) (contourConjugator vertical negative),
    contourConjugator_square, one_mul]

/-- Normalization at both infinities is proved for every nonzero continuous-spectrum ray. -/
theorem contourJostFunction_tendsto_one (q : SchwartzMap ℝ ℂ) (vertical negative : Bool)
    (κ : ℝ) (left : Bool) :
    Tendsto (fun x => contourJostFunction q vertical negative κ left (if left then -x else x))
      atTop (𝓝 1) := by
  have ht := ((baseJostFunction_tendsto (contourSource q vertical) κ left).const_mul
    (contourConjugator vertical negative)).mul_const (contourConjugator vertical negative)
  simpa only [← contourJostFunction_conjugation, mul_one, contourConjugator_square] using ht

theorem contourJostFunction_det (q : SchwartzMap ℝ ℂ) (vertical negative : Bool)
    (κ : ℝ) (left : Bool) (x : ℝ) :
    (contourJostFunction q vertical negative κ left x).det = 1 := by
  rw [contourJostFunction, Matrix.det_mul, contourJostMatrix_det, diagonalFrame_det, mul_one]

/-- The normalized matrices solve the paper's commutator equation (2.2) on all rays. -/
theorem contourJostFunction_entry_hasDerivAt (q : SchwartzMap ℝ ℂ) (vertical negative : Bool)
    (κ : ℝ) (left : Bool) (x : ℝ) (i j : Fin 2) :
    HasDerivAt (fun y => contourJostFunction q vertical negative κ left y i j)
      ((spatialLax (deriv q x) (reflectedDerivative q x) (contourParameter vertical negative κ)*
        contourJostFunction q vertical negative κ left x-
      contourJostFunction q vertical negative κ left x*spatialLax 0 0 (contourParameter vertical negative κ)) i j) x := by
  fin_cases j
  · have he : (fun y => contourJostFunction q vertical negative κ left y i 0) =
        fun y => contourJostMatrix q vertical negative κ left y i 0*FDNLS.staggerPhase (contourSquaredParameter vertical κ) y := by
      funext y
      simp [contourJostFunction, diagonalFrame, Matrix.mul_apply, Fin.sum_univ_two]
    refine (((contourJostMatrix_entry_hasDerivAt q vertical negative κ left x i 0).fun_mul
      (FDNLS.hasDerivAt_staggerPhase (contourSquaredParameter vertical κ) x)).congr_of_eventuallyEq
      (Eventually.of_forall (fun y => congrFun he y))).congr_deriv ?_
    fin_cases i <;>
      simp [contourJostFunction, diagonalFrame, spatialLax, Matrix.mul_apply, Matrix.vecMul,
        dotProduct, Fin.sum_univ_two, contourParameter_square] <;> ring
  · have he : (fun y => contourJostFunction q vertical negative κ left y i 1) =
        fun y => contourJostMatrix q vertical negative κ left y i 1*FDNLS.staggerPhase (-(contourSquaredParameter vertical κ)) y := by
      funext y
      simp [contourJostFunction, diagonalFrame, Matrix.mul_apply, Fin.sum_univ_two]
    refine (((contourJostMatrix_entry_hasDerivAt q vertical negative κ left x i 1).fun_mul
      (FDNLS.hasDerivAt_staggerPhase (-(contourSquaredParameter vertical κ)) x)).congr_of_eventuallyEq
      (Eventually.of_forall (fun y => congrFun he y))).congr_deriv ?_
    fin_cases i <;>
      simp [contourJostFunction, diagonalFrame, spatialLax, Matrix.mul_apply, Matrix.vecMul,
        dotProduct, Fin.sum_univ_two, contourParameter_square] <;> ring

end
end GaloisForLFunctions.HTGeometry.FokasLenells
