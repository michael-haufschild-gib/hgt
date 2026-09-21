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
  simp [routeKPontryaginScalarDetMatrix]
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

namespace KRVMPaired

variable {n : Type*} [Fintype n] [DecidableEq n]


def pairedBoundary (u : n → ℂ) : Matrix n (Fin 2) ℂ :=
  fun i _ => u i

def hyperbolicBoundary : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

def pairedCompletion (B : Matrix n n ℂ) (u : n → ℂ) :
    Matrix (n ⊕ Fin 2) (n ⊕ Fin 2) ℂ :=
  GaloisForLFunctions.HTGeometry.completionOperator
    B (pairedBoundary u) hyperbolicBoundary

def boundaryChange : Matrix (Fin 2) (Fin 2) ℂ := !![1, 1; 1, -1]

def boundaryChangeInv : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 2 : ℂ) • boundaryChange

theorem boundaryChangeInv_mul_boundaryChange :
    boundaryChangeInv * boundaryChange = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [boundaryChangeInv, boundaryChange, Matrix.mul_apply, Fin.sum_univ_two]

theorem boundaryChange_mul_boundaryChangeInv :
    boundaryChange * boundaryChangeInv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [boundaryChangeInv, boundaryChange, Matrix.mul_apply, Fin.sum_univ_two]

def carrierChange : Matrix (n ⊕ Fin 2) (n ⊕ Fin 2) ℂ :=
  Matrix.fromBlocks 1 0 0 boundaryChange

def carrierChangeInv : Matrix (n ⊕ Fin 2) (n ⊕ Fin 2) ℂ :=
  Matrix.fromBlocks 1 0 0 boundaryChangeInv

theorem carrierChangeInv_mul_carrierChange :
    carrierChangeInv (n := n) * carrierChange (n := n) =
      (1 : Matrix (n ⊕ Fin 2) (n ⊕ Fin 2) ℂ) := by
  rw [carrierChangeInv, carrierChange, Matrix.fromBlocks_multiply]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.one_apply, boundaryChangeInv_mul_boundaryChange]

theorem carrierChange_mul_carrierChangeInv :
    carrierChange (n := n) * carrierChangeInv (n := n) =
      (1 : Matrix (n ⊕ Fin 2) (n ⊕ Fin 2) ℂ) := by
  rw [carrierChangeInv, carrierChange, Matrix.fromBlocks_multiply]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.one_apply, boundaryChange_mul_boundaryChangeInv]

def pairedNormSq (u : n → ℂ) : ℂ :=
  ∑ i, (starRingEnd ℂ) (u i) * u i

theorem pairedBoundary_gram (u : n → ℂ) :
    (pairedBoundary u)ᴴ * pairedBoundary u =
      fun _ _ => pairedNormSq u := by
  ext i j
  simp [pairedBoundary, pairedNormSq, Matrix.mul_apply]

theorem completionY_paired (u : n → ℂ) :
    GaloisForLFunctions.HTGeometry.completionY
        (pairedBoundary u) hyperbolicBoundary =
      fun i j => if i = 0 then
        -Complex.I / 2 * (starRingEnd ℂ) (u j) else
        Complex.I / 2 * (starRingEnd ℂ) (u j) := by
  ext i j
  fin_cases i <;>
    simp [GaloisForLFunctions.HTGeometry.completionY,
      pairedBoundary, hyperbolicBoundary, Matrix.mul_apply, Fin.sum_univ_two] <;>
    ring

theorem pairedNormSq_weighted (u : n → ℂ) (c : ℂ) :
    (∑ x, c * (starRingEnd ℂ) (u x) * u x) = c * pairedNormSq u := by
  rw [pairedNormSq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem pairedNormSq_star (u : n → ℂ) :
    (starRingEnd ℂ) (pairedNormSq u) = pairedNormSq u := by
  simp only [pairedNormSq, map_sum, map_mul, starRingEnd_apply, starRingEnd_self_apply]
  apply Finset.sum_congr rfl
  intro x _
  rw [star_star]
  ring

def pairedCompletionZExpected (u : n → ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![-Complex.I * pairedNormSq u / 2, -Complex.I * pairedNormSq u / 2;
    Complex.I * pairedNormSq u / 2, Complex.I * pairedNormSq u / 2]

def pairedYUMatrix (u : n → ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![-Complex.I * pairedNormSq u / 2, -Complex.I * pairedNormSq u / 2;
    Complex.I * pairedNormSq u / 2, Complex.I * pairedNormSq u / 2]

theorem completionY_mul_pairedBoundary (u : n → ℂ) :
    GaloisForLFunctions.HTGeometry.completionY
        (pairedBoundary u) hyperbolicBoundary * pairedBoundary u = pairedYUMatrix u := by
  rw [completionY_paired]
  ext i j
  fin_cases i <;> fin_cases j
  · convert pairedNormSq_weighted u (-Complex.I / 2) using 1 <;>
      simp [pairedYUMatrix, pairedBoundary, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  · convert pairedNormSq_weighted u (-Complex.I / 2) using 1 <;>
      simp [pairedYUMatrix, pairedBoundary, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  · convert pairedNormSq_weighted u (Complex.I / 2) using 1 <;>
      simp [pairedYUMatrix, pairedBoundary, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  · convert pairedNormSq_weighted u (Complex.I / 2) using 1 <;>
      simp [pairedYUMatrix, pairedBoundary, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem completionZ_paired (B : Matrix n n ℂ) (u : n → ℂ) (hB : Bᴴ = B) :
    GaloisForLFunctions.HTGeometry.completionZ
        B (pairedBoundary u) hyperbolicBoundary = pairedCompletionZExpected u := by
  have hY := completionY_mul_pairedBoundary u
  have hstarTwo : (starRingEnd ℂ) (2 : ℂ) = 2 := by
    simpa using (map_natCast (starRingEnd ℂ) 2)
  have hYstar :
      (pairedBoundary u)ᴴ *
          (GaloisForLFunctions.HTGeometry.completionY
            (pairedBoundary u) hyperbolicBoundary)ᴴ = (pairedYUMatrix u)ᴴ := by
    rw [← Matrix.conjTranspose_mul, hY]
  have hQY :
      GaloisForLFunctions.HTGeometry.completionQ
          (pairedBoundary u) hyperbolicBoundary *
          GaloisForLFunctions.HTGeometry.completionY
            (pairedBoundary u) hyperbolicBoundary * pairedBoundary u =
        GaloisForLFunctions.HTGeometry.completionQ
          (pairedBoundary u) hyperbolicBoundary * pairedYUMatrix u := by
    rw [Matrix.mul_assoc, hY]
  have hYstarQ :
      (pairedBoundary u)ᴴ *
          (GaloisForLFunctions.HTGeometry.completionY
            (pairedBoundary u) hyperbolicBoundary)ᴴ *
          GaloisForLFunctions.HTGeometry.completionQ
            (pairedBoundary u) hyperbolicBoundary =
        (pairedYUMatrix u)ᴴ *
          GaloisForLFunctions.HTGeometry.completionQ
            (pairedBoundary u) hyperbolicBoundary := by
    rw [hYstar]
  rw [GaloisForLFunctions.HTGeometry.completionZ,
    GaloisForLFunctions.HTGeometry.completionK, hB, hQY, hYstarQ,
    GaloisForLFunctions.HTGeometry.completionQ, pairedBoundary_gram]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pairedCompletionZExpected, pairedYUMatrix, hyperbolicBoundary,
      pairedNormSq_star, hstarTwo, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_two] <;>
    ring

def pairedBaseImage (B : Matrix n n ℂ) (u : n → ℂ) : Matrix n (Fin 2) ℂ :=
  fun i _ => (B.mulVec u) i

theorem base_mul_pairedBoundary (B : Matrix n n ℂ) (u : n → ℂ) :
    B * pairedBoundary u = pairedBaseImage B u := by
  ext i j
  simp [pairedBoundary, pairedBaseImage, Matrix.mul_apply, Matrix.mulVec, dotProduct]

def pairedYStarQExpected (u : n → ℂ) : Matrix n (Fin 2) ℂ :=
  fun i _ => Complex.I / 2 * u i

theorem completionY_star_mul_Q_paired (u : n → ℂ) :
    (GaloisForLFunctions.HTGeometry.completionY
      (pairedBoundary u) hyperbolicBoundary)ᴴ *
      GaloisForLFunctions.HTGeometry.completionQ
        (pairedBoundary u) hyperbolicBoundary = pairedYStarQExpected u := by
  rw [GaloisForLFunctions.HTGeometry.completionQ, pairedBoundary_gram,
    completionY_paired]
  have hstarTwo : (starRingEnd ℂ) (2 : ℂ) = 2 := by
    simpa using (map_natCast (starRingEnd ℂ) 2)
  ext i j
  fin_cases j
  · simp [pairedYStarQExpected, hyperbolicBoundary,
      hstarTwo, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
    ring
  · simp [pairedYStarQExpected, hyperbolicBoundary,
      hstarTwo, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
    ring

theorem pairedBoundary_mul_completionZ (B : Matrix n n ℂ) (u : n → ℂ)
    (hB : Bᴴ = B) :
    pairedBoundary u * GaloisForLFunctions.HTGeometry.completionZ
      B (pairedBoundary u) hyperbolicBoundary = 0 := by
  rw [completionZ_paired B u hB]
  ext i j
  fin_cases j <;>
    simp [pairedBoundary, pairedCompletionZExpected, Matrix.mul_apply,
      Matrix.vecMul, dotProduct, Fin.sum_univ_two] <;>
    ring

def pairedCompletionXExpected (B : Matrix n n ℂ) (u : n → ℂ) : Matrix n (Fin 2) ℂ :=
  fun i _ => (B.mulVec u) i + Complex.I / 2 * u i

theorem completionX_paired (B : Matrix n n ℂ) (u : n → ℂ) (hB : Bᴴ = B) :
    GaloisForLFunctions.HTGeometry.completionX
      B (pairedBoundary u) hyperbolicBoundary = pairedCompletionXExpected B u := by
  rw [GaloisForLFunctions.HTGeometry.completionX, hB,
    base_mul_pairedBoundary, completionY_star_mul_Q_paired,
    pairedBoundary_mul_completionZ B u hB]
  ext i j
  simp [pairedBaseImage, pairedYStarQExpected, pairedCompletionXExpected]

def pairedTriangularX (B : Matrix n n ℂ) (u : n → ℂ) : Matrix n (Fin 2) ℂ :=
  fun i j => if j = 0 then
    2 * ((B.mulVec u) i + Complex.I / 2 * u i) else 0

def pairedTriangularY (u : n → ℂ) : Matrix (Fin 2) n ℂ :=
  fun i j => if i = 0 then 0 else -Complex.I / 2 * (starRingEnd ℂ) (u j)

def pairedTriangularZ (u : n → ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 0; -Complex.I * pairedNormSq u, 0]

def pairedTriangularCompletion (B : Matrix n n ℂ) (u : n → ℂ) :
    Matrix (n ⊕ Fin 2) (n ⊕ Fin 2) ℂ :=
  Matrix.fromBlocks B (pairedTriangularX B u) (pairedTriangularY u) (pairedTriangularZ u)

theorem pairedCompletion_conjugate_triangular
    (B : Matrix n n ℂ) (u : n → ℂ) (hB : Bᴴ = B) :
    carrierChangeInv * pairedCompletion B u * carrierChange =
      pairedTriangularCompletion B u := by
  rw [carrierChangeInv, pairedCompletion, carrierChange,
    GaloisForLFunctions.HTGeometry.completionOperator,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply,
    completionX_paired B u hB, completionY_paired,
    completionZ_paired B u hB]
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · simp [pairedTriangularCompletion]
  · fin_cases j <;>
      simp [pairedTriangularCompletion, pairedTriangularX, pairedCompletionXExpected,
        boundaryChange, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two] <;>
      ring
  · fin_cases i <;>
      simp [pairedTriangularCompletion, pairedTriangularY,
        boundaryChangeInv, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two] <;>
      norm_num [boundaryChange] <;>
      ring
  · fin_cases i <;> fin_cases j <;>
      simp [pairedTriangularCompletion, pairedTriangularZ,
        boundaryChange, boundaryChangeInv, pairedCompletionZExpected,
        Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two] <;>
      ring


end KRVMPaired
end

end RHTower
