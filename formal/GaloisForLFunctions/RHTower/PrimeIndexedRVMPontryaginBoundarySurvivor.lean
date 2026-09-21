import GaloisForLFunctions.HTGeometry.PontryaginBoundaryCompletion
import GaloisForLFunctions.HTGeometry.KammeyerDeterminantApproximationCore
import GaloisForLFunctions.RHTower.XiPrimeMarkedPhysicalEndpointRVMQuadraticIncidence

/-!
# K-RVM Pontryagin determinant survivor

The bounded-similarity obstruction leaves non-similarity boundary assemblies as
the K-RVM alternative.  A determinant-only exclusion of that alternative is
false: the explicit hyperbolic two-channel completion below is nonzero,
metric-self-adjoint, cubic nilpotent, and contributes one to every finite
determinant.  It is an exact obstruction to that false no-go, not an Xi
divisor identification.  The remaining K-RVM problem is to derive a global
prime-source boundary channel whose non-nilpotent carrier has the Xi divisor.
-/

open Complex Matrix
open scoped Matrix

namespace RHTower

noncomputable section

def routeKPontryaginBase : Matrix (Fin 1) (Fin 1) ℂ := 0
def routeKPontryaginBoundary : Matrix (Fin 1) (Fin 2) ℂ := !![1, 1]
def routeKPontryaginHyperbolic : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

theorem routeKPontryaginHyperbolic_herm :
    routeKPontryaginHyperbolicᴴ = routeKPontryaginHyperbolic := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [routeKPontryaginHyperbolic]

theorem routeKPontryaginHyperbolic_sq :
    routeKPontryaginHyperbolic * routeKPontryaginHyperbolic = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [routeKPontryaginHyperbolic, Matrix.mul_apply, Fin.sum_univ_two]

theorem routeKPontryagin_selfAdjoint_defect :
    routeKPontryaginBase - routeKPontryaginBaseᴴ =
      (GaloisForLFunctions.HTGeometry.completionY
        routeKPontryaginBoundary routeKPontryaginHyperbolic)ᴴ *
          routeKPontryaginBoundaryᴴ -
        routeKPontryaginBoundary *
          GaloisForLFunctions.HTGeometry.completionY
            routeKPontryaginBoundary routeKPontryaginHyperbolic := by
  ext i j
  fin_cases i; fin_cases j
  simp [routeKPontryaginBase, routeKPontryaginBoundary,
      routeKPontryaginHyperbolic,
      GaloisForLFunctions.HTGeometry.completionY, Matrix.mul_apply,
      Matrix.vecMul, dotProduct, Fin.sum_univ_two]

def routeKPontryaginCompletion : Matrix (Fin 1 ⊕ Fin 2) (Fin 1 ⊕ Fin 2) ℂ :=
  GaloisForLFunctions.HTGeometry.completionOperator
    routeKPontryaginBase routeKPontryaginBoundary routeKPontryaginHyperbolic

def routeKPontryaginNilpotent : Matrix (Fin 1 ⊕ Fin 2) (Fin 1 ⊕ Fin 2) ℂ
  | .inl _, .inl _ => 0
  | .inl _, .inr _ => Complex.I / 2
  | .inr 0, .inl _ => -Complex.I / 2
  | .inr 1, .inl _ => Complex.I / 2
  | .inr 0, .inr _ => -Complex.I / 2
  | .inr 1, .inr _ => Complex.I / 2

theorem routeKPontryaginCompletion_eq_nilpotent :
    routeKPontryaginCompletion = routeKPontryaginNilpotent := by
  have hstarTwo : (starRingEnd ℂ) (2 : ℂ) = 2 := by
    simpa using (map_natCast (starRingEnd ℂ) 2)
  ext i j
  rcases i with i | i <;> rcases j with j | j
  all_goals
    fin_cases i <;> fin_cases j
    all_goals
      simp [routeKPontryaginCompletion, routeKPontryaginNilpotent,
        GaloisForLFunctions.HTGeometry.completionOperator,
        GaloisForLFunctions.HTGeometry.completionX,
        GaloisForLFunctions.HTGeometry.completionY,
        GaloisForLFunctions.HTGeometry.completionZ,
        GaloisForLFunctions.HTGeometry.completionK,
        GaloisForLFunctions.HTGeometry.completionQ,
        routeKPontryaginBase, routeKPontryaginBoundary,
        routeKPontryaginHyperbolic, Matrix.mul_apply,
        Matrix.vecMul, dotProduct, Fin.sum_univ_two, hstarTwo] <;>
        ring

theorem routeKPontryaginCompletion_cube :
    routeKPontryaginCompletion * routeKPontryaginCompletion *
      routeKPontryaginCompletion = 0 := by
  rw [routeKPontryaginCompletion_eq_nilpotent]
  ext i j
  rcases i with i | i <;> rcases j with j | j
  all_goals
    fin_cases i; fin_cases j
    all_goals
      simp [routeKPontryaginNilpotent, Matrix.mul_apply, Fintype.sum_sum_type,
        Fin.sum_univ_two];
      ring

theorem routeKPontryaginCompletion_det_one (z : ℂ) :
    ((1 : Matrix (Fin 1 ⊕ Fin 2) (Fin 1 ⊕ Fin 2) ℂ) -
      z • routeKPontryaginCompletion).det = 1 := by
  apply GaloisForLFunctions.HTGeometry.Kammeyer.det_one_sub_smul_of_pow_eq_zero
    routeKPontryaginCompletion 3
  simpa [pow_succ, pow_two] using routeKPontryaginCompletion_cube

theorem routeKPontryaginCompletion_nonzero : routeKPontryaginCompletion ≠ 0 := by
  intro h
  have hentry := congr_fun (congr_fun h (Sum.inr 0)) (Sum.inl 0)
  norm_num [routeKPontryaginCompletion,
    GaloisForLFunctions.HTGeometry.completionOperator,
    GaloisForLFunctions.HTGeometry.completionY, routeKPontryaginBase,
    routeKPontryaginBoundary, routeKPontryaginHyperbolic,
    Matrix.vecMul, dotProduct, Fin.sum_univ_two] at hentry

theorem routeKPontryaginCompletion_metric_adjoint :
    GaloisForLFunctions.HTGeometry.completionMetric
        routeKPontryaginBoundary routeKPontryaginHyperbolic *
      routeKPontryaginCompletion =
      routeKPontryaginCompletionᴴ *
        GaloisForLFunctions.HTGeometry.completionMetric
          routeKPontryaginBoundary routeKPontryaginHyperbolic := by
  apply GaloisForLFunctions.HTGeometry.completion_metric_adjoint
  · exact routeKPontryagin_selfAdjoint_defect
  · exact routeKPontryaginHyperbolic_herm
  · exact routeKPontryaginHyperbolic_sq

/-- Reindex the one-prime plus two-boundary completion as a three-dimensional matrix. -/
def routeKPontryaginIndexEquiv : Fin 1 ⊕ Fin 2 ≃ Fin 3 where
  toFun := Sum.elim (Fin.castAdd 2) (Fin.natAdd 1)
  invFun := fun i =>
    Fin.addCases Sum.inl Sum.inr (Fin.cast (by omega : 3 = 1 + 2) i)
  left_inv := by
    rintro (i | j) <;> simp
  right_inv := by
    intro i
    fin_cases i <;> rfl

/-- Real scalar source compression on one prime coordinate. -/
def routeKPontryaginScalarBase (b : ℝ) : Matrix (Fin 1) (Fin 1) ℂ := !![(b : ℂ)]

/-- The hyperbolic two-channel completion of a real one-prime scalar compression. -/
def routeKPontryaginScalarCompletion (b : ℝ) :
    Matrix (Fin 1 ⊕ Fin 2) (Fin 1 ⊕ Fin 2) ℂ :=
  GaloisForLFunctions.HTGeometry.completionOperator
    (routeKPontryaginScalarBase b) routeKPontryaginBoundary routeKPontryaginHyperbolic

/-- Explicit matrix of the scalar completion. -/
def routeKPontryaginScalarCompletionExplicit (b : ℝ) :
    Matrix (Fin 1 ⊕ Fin 2) (Fin 1 ⊕ Fin 2) ℂ
  | .inl _, .inl _ => b
  | .inl _, .inr _ => b + Complex.I / 2
  | .inr 0, .inl _ => -Complex.I / 2
  | .inr 1, .inl _ => Complex.I / 2
  | .inr 0, .inr _ => -Complex.I / 2
  | .inr 1, .inr _ => Complex.I / 2

theorem routeKPontryaginScalarCompletion_eq_explicit (b : ℝ) :
    routeKPontryaginScalarCompletion b = routeKPontryaginScalarCompletionExplicit b := by
  have hstarTwo : (starRingEnd ℂ) (2 : ℂ) = 2 := by
    simpa using (map_natCast (starRingEnd ℂ) 2)
  ext i j
  rcases i with i | i <;> rcases j with j | j
  all_goals
    fin_cases i <;> fin_cases j
    all_goals
      simp [routeKPontryaginScalarCompletion, routeKPontryaginScalarCompletionExplicit,
        routeKPontryaginScalarBase,
        GaloisForLFunctions.HTGeometry.completionOperator,
        GaloisForLFunctions.HTGeometry.completionX,
        GaloisForLFunctions.HTGeometry.completionY,
        GaloisForLFunctions.HTGeometry.completionZ,
        GaloisForLFunctions.HTGeometry.completionK,
        GaloisForLFunctions.HTGeometry.completionQ,
        routeKPontryaginBoundary, routeKPontryaginHyperbolic,
        Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, hstarTwo] <;>
        ring

/-- Determinant matrix of the scalar completion after the canonical three-point reindexing. -/
def routeKPontryaginScalarDetMatrix (b : ℝ) (z : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1 - z * (b : ℂ), -z * ((b : ℂ) + Complex.I / 2),
      -z * ((b : ℂ) + Complex.I / 2);
    z * Complex.I / 2, 1 + z * Complex.I / 2, z * Complex.I / 2;
    -z * Complex.I / 2, -z * Complex.I / 2, 1 - z * Complex.I / 2]

theorem reindex_routeKPontryaginScalar_detMatrix (b : ℝ) (z : ℂ) :
    Matrix.reindex routeKPontryaginIndexEquiv routeKPontryaginIndexEquiv
      ((1 : Matrix (Fin 1 ⊕ Fin 2) (Fin 1 ⊕ Fin 2) ℂ) -
        z • routeKPontryaginScalarCompletion b) =
      routeKPontryaginScalarDetMatrix b z := by
  rw [routeKPontryaginScalarCompletion_eq_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.reindex, routeKPontryaginIndexEquiv,
      routeKPontryaginScalarCompletionExplicit, routeKPontryaginScalarDetMatrix,
      Fin.addCases] <;>
    ring

/-- The nontrivial hyperbolic boundary completion preserves the scalar Fredholm determinant
exactly. -/
theorem routeKPontryaginScalarCompletion_det (b : ℝ) (z : ℂ) :
    ((1 : Matrix (Fin 1 ⊕ Fin 2) (Fin 1 ⊕ Fin 2) ℂ) -
      z • routeKPontryaginScalarCompletion b).det = 1 - z * (b : ℂ) := by
  rw [← Matrix.det_reindex_self routeKPontryaginIndexEquiv,
    reindex_routeKPontryaginScalar_detMatrix]
  rw [Matrix.det_fin_three]
  simp [routeKPontryaginScalarDetMatrix] <;>
    ring

theorem routeKPontryaginScalar_selfAdjoint_defect (b : ℝ) :
    routeKPontryaginScalarBase b - (routeKPontryaginScalarBase b)ᴴ =
      (GaloisForLFunctions.HTGeometry.completionY
        routeKPontryaginBoundary routeKPontryaginHyperbolic)ᴴ *
          routeKPontryaginBoundaryᴴ -
        routeKPontryaginBoundary *
          GaloisForLFunctions.HTGeometry.completionY
            routeKPontryaginBoundary routeKPontryaginHyperbolic := by
  ext i j
  fin_cases i; fin_cases j
  simp [routeKPontryaginScalarBase, routeKPontryaginBoundary,
    routeKPontryaginHyperbolic,
    GaloisForLFunctions.HTGeometry.completionY, Matrix.mul_apply,
    Matrix.vecMul, dotProduct, Fin.sum_univ_two]

theorem routeKPontryaginScalarCompletion_metric_adjoint (b : ℝ) :
    GaloisForLFunctions.HTGeometry.completionMetric
        routeKPontryaginBoundary routeKPontryaginHyperbolic *
      routeKPontryaginScalarCompletion b =
      (routeKPontryaginScalarCompletion b)ᴴ *
        GaloisForLFunctions.HTGeometry.completionMetric
          routeKPontryaginBoundary routeKPontryaginHyperbolic := by
  apply GaloisForLFunctions.HTGeometry.completion_metric_adjoint
  · exact routeKPontryaginScalar_selfAdjoint_defect b
  · exact routeKPontryaginHyperbolic_herm
  · exact routeKPontryaginHyperbolic_sq

/-- Source-marked scalar completion at every admitted prime diagonal. -/
def routeKPrimeDiagonalPontryaginCompletion (p : Nat.Primes) :
    Matrix (Fin 1 ⊕ Fin 2) (Fin 1 ⊕ Fin 2) ℂ :=
  routeKPontryaginScalarCompletion (routeKQuadraticallyAdmittedDiagonalWeight p)

/-- Every literal admitted prime diagonal has a non-similarity hyperbolic completion which
preserves its determinant exactly. -/
theorem routeKPrimeDiagonalPontryaginCompletion_det
    (p : Nat.Primes) (z : ℂ) :
    ((1 : Matrix (Fin 1 ⊕ Fin 2) (Fin 1 ⊕ Fin 2) ℂ) -
      z • routeKPrimeDiagonalPontryaginCompletion p).det =
      1 - z * (routeKQuadraticallyAdmittedDiagonalWeight p : ℂ) := by
  exact routeKPontryaginScalarCompletion_det
    (routeKQuadraticallyAdmittedDiagonalWeight p) z

theorem routeKPrimeDiagonalPontryaginCompletion_metric_adjoint
    (p : Nat.Primes) :
    GaloisForLFunctions.HTGeometry.completionMetric
        routeKPontryaginBoundary routeKPontryaginHyperbolic *
      routeKPrimeDiagonalPontryaginCompletion p =
      (routeKPrimeDiagonalPontryaginCompletion p)ᴴ *
        GaloisForLFunctions.HTGeometry.completionMetric
          routeKPontryaginBoundary routeKPontryaginHyperbolic := by
  exact routeKPontryaginScalarCompletion_metric_adjoint
    (routeKQuadraticallyAdmittedDiagonalWeight p)

end

end RHTower
