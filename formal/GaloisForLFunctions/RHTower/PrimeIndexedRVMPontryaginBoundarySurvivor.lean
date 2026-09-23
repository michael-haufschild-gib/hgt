import GaloisForLFunctions.HTGeometry.PontryaginBoundaryCompletion
import GaloisForLFunctions.HTGeometry.KammeyerDeterminantApproximationCore
import GaloisForLFunctions.HTGeometry.RegularizedDeterminantAlgebraicMultiplicity
import GaloisForLFunctions.HTGeometry.CompactSelfAdjointEigenvalue
import GaloisForLFunctions.HTGeometry.HermitianDilationSecondJetObstruction
import GaloisForLFunctions.HTGeometry.HilbertSchmidtFourthJet
import GaloisForLFunctions.HTGeometry.RegularizedResolventTraceOperator
import GaloisForLFunctions.RHTower.PrimeArchThetaAllOrderCumulant
import GaloisForLFunctions.RHTower.XiPrimeMarkedPhysicalEndpointRVMQuadraticIncidence
import GaloisForLFunctions.RHTower.XiPrimeMarkedPhysicalEndpointRVMQuarticIncidence
import GaloisForLFunctions.RHTower.PrimeIndexedRVMQuarticCubicTrace
import GaloisForLFunctions.HTGeometry.EvenEntireSquareFactor

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


def triangularIndexEquiv : n ⊕ Fin 2 ≃ (n ⊕ Fin 1) ⊕ Fin 1 where
  toFun := fun x => match x with
    | .inl i => .inl (.inl i)
    | .inr j => Fin.cases (.inl (.inr 0)) (fun _ => .inr 0) j
  invFun := fun x => match x with
    | .inl (.inl i) => .inl i
    | .inl (.inr _) => .inr 0
    | .inr _ => .inr 1
  left_inv := by
    rintro (i | j)
    · rfl
    · fin_cases j <;> rfl
  right_inv := by
    rintro ((i | j) | k)
    · rfl
    · fin_cases j <;> rfl
    · fin_cases k <;> rfl

def triangularX0 (B : Matrix n n ℂ) (u : n → ℂ) : Matrix n (Fin 1) ℂ :=
  fun i _ => pairedTriangularX B u i 0

def triangularY1 (u : n → ℂ) : Matrix (Fin 1) n ℂ :=
  fun _ j => pairedTriangularY u 1 j

def triangularZ10 (u : n → ℂ) : Matrix (Fin 1) (Fin 1) ℂ :=
  fun _ _ => pairedTriangularZ u 1 0

def triangularLower (u : n → ℂ) (z : ℂ) : Matrix (Fin 1) (n ⊕ Fin 1) ℂ
  | i, .inl j => -z * triangularY1 u i j
  | i, .inr j => -z * triangularZ10 u i j

def triangularReindexRhs (B : Matrix n n ℂ) (u : n → ℂ) (z : ℂ) :
    Matrix ((n ⊕ Fin 1) ⊕ Fin 1) ((n ⊕ Fin 1) ⊕ Fin 1) ℂ :=
  Matrix.fromBlocks
    (Matrix.fromBlocks ((1 : Matrix n n ℂ) - z • B) (-z • triangularX0 B u) 0 1)
    0
    (triangularLower u z)
    1

theorem reindex_triangular_resolvent
    (B : Matrix n n ℂ) (u : n → ℂ) (z : ℂ) :
    Matrix.reindex triangularIndexEquiv triangularIndexEquiv
      ((1 : Matrix (n ⊕ Fin 2) (n ⊕ Fin 2) ℂ) -
        z • pairedTriangularCompletion B u) = triangularReindexRhs B u z := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · rcases i with i | i <;> rcases j with j | j
    · simp [Matrix.reindex, triangularIndexEquiv, triangularReindexRhs,
        pairedTriangularCompletion, pairedTriangularX, pairedTriangularY, pairedTriangularZ, triangularLower, Matrix.one_apply]
    · fin_cases j
      simp [Matrix.reindex, triangularIndexEquiv, triangularReindexRhs,
        triangularX0, pairedTriangularCompletion, pairedTriangularX, pairedTriangularY, pairedTriangularZ, triangularLower, Matrix.one_apply]
    · fin_cases i
      simp [Matrix.reindex, triangularIndexEquiv, triangularReindexRhs,
        pairedTriangularCompletion, pairedTriangularX, pairedTriangularY, pairedTriangularZ, triangularLower, Matrix.one_apply]
    · fin_cases i <;> fin_cases j
      simp [Matrix.reindex, triangularIndexEquiv, triangularReindexRhs,
        triangularX0, pairedTriangularCompletion, pairedTriangularX, pairedTriangularY, pairedTriangularZ, triangularLower, Matrix.one_apply]
  · rcases i with i | i <;> fin_cases j
    · simp [Matrix.reindex, triangularIndexEquiv, triangularReindexRhs,
        pairedTriangularCompletion, pairedTriangularX, pairedTriangularY, pairedTriangularZ, triangularLower, Matrix.one_apply]
    · fin_cases i
      simp [Matrix.reindex, triangularIndexEquiv, triangularReindexRhs,
        pairedTriangularCompletion, pairedTriangularX, pairedTriangularY, pairedTriangularZ, triangularLower, Matrix.one_apply]
  · fin_cases i
    rcases j with j | j
    · simp [Matrix.reindex, triangularIndexEquiv, triangularReindexRhs,
          triangularY1, pairedTriangularCompletion, pairedTriangularX, pairedTriangularY, pairedTriangularZ, triangularLower, Matrix.one_apply]
    · fin_cases j
      simp [Matrix.reindex, triangularIndexEquiv, triangularReindexRhs,
        triangularZ10, pairedTriangularCompletion, pairedTriangularX, pairedTriangularY, pairedTriangularZ, triangularLower, Matrix.one_apply]
  · fin_cases i <;> fin_cases j
    simp [Matrix.reindex, triangularIndexEquiv, triangularReindexRhs,
      pairedTriangularCompletion, pairedTriangularX, pairedTriangularY, pairedTriangularZ, triangularLower, Matrix.one_apply]

theorem triangularReindexRhs_det (B : Matrix n n ℂ) (u : n → ℂ) (z : ℂ) :
    (triangularReindexRhs B u z).det =
      ((1 : Matrix n n ℂ) - z • B).det := by
  rw [triangularReindexRhs, Matrix.det_fromBlocks_zero₁₂,
    Matrix.det_fromBlocks_zero₂₁]
  simp

theorem pairedTriangularCompletion_det (B : Matrix n n ℂ) (u : n → ℂ) (z : ℂ) :
    ((1 : Matrix (n ⊕ Fin 2) (n ⊕ Fin 2) ℂ) -
      z • pairedTriangularCompletion B u).det =
      ((1 : Matrix n n ℂ) - z • B).det := by
  rw [← Matrix.det_reindex_self triangularIndexEquiv,
    reindex_triangular_resolvent]
  exact triangularReindexRhs_det B u z

theorem det_conj_general {m : Type*} [Fintype m] [DecidableEq m]
    (P Q : Matrix m m ℂ) (h : Q * P = 1) (Y : Matrix m m ℂ) :
    (Q * Y * P).det = Y.det := by
  have hdet : Q.det * P.det = 1 := by
    have := congrArg Matrix.det h
    rwa [Matrix.det_mul, Matrix.det_one] at this
  rw [Matrix.det_mul, Matrix.det_mul]
  calc
    Q.det * Y.det * P.det = Q.det * P.det * Y.det := by ring
    _ = Y.det := by rw [hdet, one_mul]

theorem pairedCompletion_det (B : Matrix n n ℂ) (u : n → ℂ) (hB : Bᴴ = B)
    (z : ℂ) :
    ((1 : Matrix (n ⊕ Fin 2) (n ⊕ Fin 2) ℂ) - z • pairedCompletion B u).det =
      ((1 : Matrix n n ℂ) - z • B).det := by
  have hmatrix :
      carrierChangeInv *
          ((1 : Matrix (n ⊕ Fin 2) (n ⊕ Fin 2) ℂ) - z • pairedCompletion B u) *
          carrierChange =
        (1 : Matrix (n ⊕ Fin 2) (n ⊕ Fin 2) ℂ) -
          z • pairedTriangularCompletion B u := by
    calc
      carrierChangeInv *
          ((1 : Matrix (n ⊕ Fin 2) (n ⊕ Fin 2) ℂ) - z • pairedCompletion B u) *
          carrierChange =
        carrierChangeInv * carrierChange -
          z • (carrierChangeInv * pairedCompletion B u * carrierChange) := by
            calc
              carrierChangeInv *
                  ((1 : Matrix (n ⊕ Fin 2) (n ⊕ Fin 2) ℂ) -
                    z • pairedCompletion B u) * carrierChange =
                  (carrierChangeInv -
                    z • (carrierChangeInv * pairedCompletion B u)) * carrierChange := by
                      rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul]
              _ = carrierChangeInv * carrierChange -
                  z • (carrierChangeInv * pairedCompletion B u * carrierChange) := by
                    rw [Matrix.sub_mul, smul_mul_assoc]
      _ = (1 : Matrix (n ⊕ Fin 2) (n ⊕ Fin 2) ℂ) -
          z • pairedTriangularCompletion B u := by
        rw [carrierChangeInv_mul_carrierChange,
          pairedCompletion_conjugate_triangular B u hB]
  calc
    ((1 : Matrix (n ⊕ Fin 2) (n ⊕ Fin 2) ℂ) - z • pairedCompletion B u).det =
        (carrierChangeInv *
          ((1 : Matrix (n ⊕ Fin 2) (n ⊕ Fin 2) ℂ) - z • pairedCompletion B u) *
            carrierChange).det :=
      (det_conj_general (carrierChange (n := n)) (carrierChangeInv (n := n))
        (carrierChangeInv_mul_carrierChange (n := n)) _).symm
    _ = ((1 : Matrix (n ⊕ Fin 2) (n ⊕ Fin 2) ℂ) -
        z • pairedTriangularCompletion B u).det := congrArg Matrix.det hmatrix
    _ = ((1 : Matrix n n ℂ) - z • B).det := pairedTriangularCompletion_det B u z


def routeKFiniteCompression (f : n → Nat.Primes) : Matrix n n ℂ :=
  fun i j => inner ℂ (routeKPrimeBasis (f i))
    (routeKQuadraticallyAdmittedOperator (routeKPrimeBasis (f j)))

omit [Fintype n] [DecidableEq n] in
theorem routeKFiniteCompression_hermitian (f : n → Nat.Primes) :
    (routeKFiniteCompression f)ᴴ = routeKFiniteCompression f := by
  ext i j
  simp only [Matrix.conjTranspose_apply, routeKFiniteCompression]
  rw [← starRingEnd_apply, inner_conj_symm]
  exact (routeKQuadraticallyAdmittedOperator_isSelfAdjoint.isSymmetric _ _)

theorem routeKFiniteCompression_pairedCompletion_det
    (f : n → Nat.Primes) (u : n → ℂ) (z : ℂ) :
    ((1 : Matrix (n ⊕ Fin 2) (n ⊕ Fin 2) ℂ) -
        z • pairedCompletion (routeKFiniteCompression f) u).det =
      ((1 : Matrix n n ℂ) - z • routeKFiniteCompression f).det :=
  pairedCompletion_det (routeKFiniteCompression f) u
    (routeKFiniteCompression_hermitian f) z

def routeKNthPrimeTripleCompression (n : ℕ) : Matrix (Fin 3) (Fin 3) ℂ :=
  routeKFiniteCompression ![nthPrimeSubtype n, nthPrimeSubtype (n + 1),
    nthPrimeSubtype (n + 2)]

theorem exists_cofinal_nonzero_routeKNthPrimeTripleCompression_holonomy (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧
      routeKNthPrimeTripleCompression n 0 1 *
        routeKNthPrimeTripleCompression n 1 2 *
        routeKNthPrimeTripleCompression n 2 0 ≠ 0 := by
  obtain ⟨n, hn, hcycle⟩ :=
    exists_cofinal_nonzero_quadraticallyAdmitted_triangleHolonomy N
  exact ⟨n, hn, by
    simpa [routeKNthPrimeTripleCompression, routeKFiniteCompression] using hcycle⟩


def routeKQuadraticallyAdmittedKernel : Nat.Primes × Nat.Primes → ℂ :=
  HilbertSchmidt.matrixOf routeKQuadraticallyAdmittedOperator

theorem routeKQuadraticallyAdmittedKernel_isHS :
    HilbertSchmidt.IsHS routeKQuadraticallyAdmittedKernel := by
  exact HilbertSchmidt.isHS_matrixOf
    routeKQuadraticallyAdmittedOperator_isHilbertSchmidt

theorem routeKQuadraticallyAdmittedKernel_toOperator :
    HilbertSchmidt.toOperator routeKQuadraticallyAdmittedKernel_isHS =
      routeKQuadraticallyAdmittedOperator := by
  simpa [routeKQuadraticallyAdmittedKernel] using
    (HilbertSchmidt.toOperator_matrixOf
      routeKQuadraticallyAdmittedOperator_isHilbertSchmidt)

theorem routeKQuadraticallyAdmittedKernel_isSelfAdjoint :
    IsSelfAdjoint
      (HilbertSchmidt.toOperator routeKQuadraticallyAdmittedKernel_isHS) := by
  rw [routeKQuadraticallyAdmittedKernel_toOperator]
  exact routeKQuadraticallyAdmittedOperator_isSelfAdjoint


noncomputable def routeKQuadraticallyAdmittedEntireDet : ℂ → ℂ :=
  GaloisForLFunctions.HTGeometry.entireDet2
    routeKQuadraticallyAdmittedKernel

theorem exists_routeKQuadraticallyAdmittedEntireDet_real_zero :
    ∃ z : ℂ, z ≠ 0 ∧ z.im = 0 ∧ routeKQuadraticallyAdmittedEntireDet z = 0 := by
  have hnormpos : 0 < ContinuousLinearMap.hsNormSq
      routeKQuadraticallyAdmittedOperator := by
    nlinarith [two_mul_hsNormSq_routeKQuadraticallyAdmittedOperator,
      routeKSourceZerothMoment_pos]
  have hTne : routeKQuadraticallyAdmittedOperator ≠ 0 := by
    intro hzero
    exact (ne_of_gt hnormpos)
      ((ContinuousLinearMap.hsNormSq_eq_zero_iff
        routeKQuadraticallyAdmittedOperator_isHilbertSchmidt).mpr hzero)
  obtain ⟨μ, x, hμnorm, hxnorm, hxeig⟩ :=
    ContinuousLinearMap.exists_unit_eigenvector_norm
      routeKQuadraticallyAdmittedOperator_isHilbertSchmidt.isCompactOperator
      routeKQuadraticallyAdmittedOperator_isSelfAdjoint.isSymmetric hTne
  have hμne : μ ≠ 0 := by
    intro hμzero
    rw [hμzero, abs_zero] at hμnorm
    exact hTne (norm_eq_zero.mp hμnorm.symm)
  refine ⟨(μ : ℂ)⁻¹, inv_ne_zero (Complex.ofReal_ne_zero.mpr hμne), by simp, ?_⟩
  unfold routeKQuadraticallyAdmittedEntireDet
  apply (GaloisForLFunctions.HTGeometry.entireDet2_eq_zero_iff_exists_eigenvector
    routeKQuadraticallyAdmittedKernel_isHS
    (inv_ne_zero (Complex.ofReal_ne_zero.mpr hμne))).mpr
  refine ⟨x, ?_, ?_⟩
  · intro hxzero
    rw [hxzero, norm_zero] at hxnorm
    norm_num at hxnorm
  · rw [routeKQuadraticallyAdmittedKernel_toOperator, inv_inv]
    exact hxeig


theorem routeKQuadraticallyAdmittedEntireDet_zero_im {z : ℂ}
    (hz : routeKQuadraticallyAdmittedEntireDet z = 0) : z.im = 0 := by
  have hz0 : z ≠ 0 := by
    intro hzero
    subst z
    have hone :=
      (GaloisForLFunctions.HTGeometry.isRegularizedDet_entireDet2
        routeKQuadraticallyAdmittedKernel_isHS).eq_one_at_zero
    exact one_ne_zero (hone.symm.trans hz)
  obtain ⟨w, hw0, hw⟩ :=
    (GaloisForLFunctions.HTGeometry.entireDet2_eq_zero_iff_exists_eigenvector
      routeKQuadraticallyAdmittedKernel_isHS hz0).mp hz
  have heig : Module.End.HasEigenvalue
      (HilbertSchmidt.toOperator routeKQuadraticallyAdmittedKernel_isHS :
        Module.End ℂ RouteKPrimeHilbert) z⁻¹ :=
    Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr hw, hw0⟩
  have hsymm :
      (HilbertSchmidt.toOperator routeKQuadraticallyAdmittedKernel_isHS :
        Module.End ℂ RouteKPrimeHilbert).IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      routeKQuadraticallyAdmittedKernel_isSelfAdjoint
  have hrealInv : star z⁻¹ = z⁻¹ := hsymm.conj_eigenvalue_eq_self heig
  have himInv : z⁻¹.im = 0 := Complex.conj_eq_iff_im.mp hrealInv
  rw [Complex.inv_im] at himInv
  have hnorm : Complex.normSq z ≠ 0 := (Complex.normSq_pos.mpr hz0).ne'
  exact neg_eq_zero.mp (div_eq_zero_iff.mp himInv |>.resolve_right hnorm)


/-- The kernel-side square trace is exactly the operator square trace of the source carrier. -/
theorem routeKQuadraticallyAdmittedKernel_square_trace :
    (∑' p : Nat.Primes,
      HilbertSchmidt.hsPow routeKQuadraticallyAdmittedKernel 1 (p, p)) =
      ContinuousLinearMap.opTrace (routeKQuadraticallyAdmittedOperator ^ (2 : ℕ)) := by
  rw [show HilbertSchmidt.hsPow routeKQuadraticallyAdmittedKernel 1 =
      HilbertSchmidt.hsComp routeKQuadraticallyAdmittedKernel
        routeKQuadraticallyAdmittedKernel by rfl]
  rw [← HilbertSchmidt.opTrace_toOperator_comp
    routeKQuadraticallyAdmittedKernel_isHS routeKQuadraticallyAdmittedKernel_isHS,
    routeKQuadraticallyAdmittedKernel_toOperator]
  rfl

/-- The regularized determinant's second coefficient is fixed by the completed source moment. -/
theorem four_mul_taylorCoeff_routeKQuadraticallyAdmittedEntireDet_two :
    4 * GaloisForLFunctions.HTGeometry.taylorCoeff
      routeKQuadraticallyAdmittedEntireDet 2 =
      -(routeKSourceZerothMoment : ℂ) := by
  rw [routeKQuadraticallyAdmittedEntireDet,
    GaloisForLFunctions.HTGeometry.taylorCoeff_entireDet2_two
      routeKQuadraticallyAdmittedKernel_isHS,
    routeKQuadraticallyAdmittedKernel_square_trace]
  have hsource := two_mul_opTrace_sq_routeKQuadraticallyAdmittedOperator
  calc
    4 * (-ContinuousLinearMap.opTrace (routeKQuadraticallyAdmittedOperator ^ (2 : ℕ)) / 2) =
        -(2 * ContinuousLinearMap.opTrace (routeKQuadraticallyAdmittedOperator ^ (2 : ℕ))) := by ring
    _ = -(routeKSourceZerothMoment : ℂ) := congrArg Neg.neg hsource

/-- The K-RVM determinant and centered Xi have the same normalized second Taylor coefficient. -/
theorem four_mul_taylorCoeff_routeKQuadraticallyAdmittedEntireDet_two_eq_Xi :
    4 * GaloisForLFunctions.HTGeometry.taylorCoeff
      routeKQuadraticallyAdmittedEntireDet 2 =
      ((deriv (deriv Xi) 0 : ℝ) : ℂ) / (Xi 0 : ℂ) := by
  rw [four_mul_taylorCoeff_routeKQuadraticallyAdmittedEntireDet_two]
  have hsource :
      (routeKSourceZerothMoment : ℂ) =
        -((deriv (deriv Xi) 0 : ℝ) : ℂ) / (Xi 0 : ℂ) := by
    norm_cast
    unfold routeKSourceZerothMoment
    exact analyticTraceMoments_normalizedPrimeArchSource_zero_eq_Xi_ratio
  rw [hsource]
  ring

/-- The first two completed prime--archimedean source moments fix Xi's normalized fourth jet. -/
theorem normalized_XiC_fourth_jet_eq_source_moments :
    iteratedDeriv 4 XiC 0 / XiC 0 / 24 =
      (normalizedPrimeArchMoment 0 : ℂ) ^ (2 : ℕ) / 8 -
        (normalizedPrimeArchMoment 1 : ℂ) / 4 := by
  have h := normalizedPrimeArchMoment_recursive 1
  norm_num [Finset.sum_range_succ, thetaCuspXiJet,
    thetaCuspPrimeArchProductJet, Nat.choose] at h
  have h0 := normalizedPrimeArchMoment_recursive 0
  norm_num [Finset.sum_range_succ, thetaCuspXiJet,
    thetaCuspPrimeArchProductJet, Nat.choose] at h0
  have hXi0 : XiC 0 = (thetaCuspRawEvenMoment 0 : ℂ) := by
    simpa using iteratedDeriv_XiC_zero_eq_rawEvenMoment 0
  have hXi4 : iteratedDeriv 4 XiC 0 = (thetaCuspRawEvenMoment 2 : ℂ) := by
    simpa using iteratedDeriv_XiC_zero_eq_rawEvenMoment 2
  rw [hXi0, hXi4]
  have hA : (thetaCuspRawEvenMoment 0 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr thetaCuspRawEvenMoment_zero_pos.ne'
  field_simp [hA]
  linear_combination 32 * h - 96 * h0 * (normalizedPrimeArchMoment 0 : ℂ)


def routeKQuarticallyAdmittedKernel : Nat.Primes × Nat.Primes → ℂ :=
  HilbertSchmidt.matrixOf routeKQuarticallyAdmittedOperator

theorem routeKQuarticallyAdmittedKernel_isHS :
    HilbertSchmidt.IsHS routeKQuarticallyAdmittedKernel := by
  exact HilbertSchmidt.isHS_matrixOf
    routeKQuarticallyAdmittedOperator_isHilbertSchmidt

theorem routeKQuarticallyAdmittedKernel_toOperator :
    HilbertSchmidt.toOperator routeKQuarticallyAdmittedKernel_isHS =
      routeKQuarticallyAdmittedOperator := by
  simpa [routeKQuarticallyAdmittedKernel] using
    (HilbertSchmidt.toOperator_matrixOf
      routeKQuarticallyAdmittedOperator_isHilbertSchmidt)

theorem routeKQuarticallyAdmittedKernel_square_trace :
    (∑' p : Nat.Primes,
      HilbertSchmidt.hsPow routeKQuarticallyAdmittedKernel 1 (p, p)) =
      ContinuousLinearMap.opTrace (routeKQuarticallyAdmittedOperator ^ (2 : ℕ)) := by
  rw [show HilbertSchmidt.hsPow routeKQuarticallyAdmittedKernel 1 =
      HilbertSchmidt.hsComp routeKQuarticallyAdmittedKernel
        routeKQuarticallyAdmittedKernel by rfl]
  rw [← HilbertSchmidt.opTrace_toOperator_comp
    routeKQuarticallyAdmittedKernel_isHS routeKQuarticallyAdmittedKernel_isHS,
    routeKQuarticallyAdmittedKernel_toOperator]
  rfl

theorem routeKQuarticallyAdmittedKernel_fourth_trace :
    (∑' p : Nat.Primes,
      HilbertSchmidt.hsPow routeKQuarticallyAdmittedKernel 3 (p, p)) =
      ContinuousLinearMap.opTrace (routeKQuarticallyAdmittedOperator ^ (4 : ℕ)) := by
  rw [← HilbertSchmidt.hsComp_hsPow
    routeKQuarticallyAdmittedKernel_isHS 1 1]
  rw [← HilbertSchmidt.opTrace_toOperator_comp
    (HilbertSchmidt.isHS_hsPow routeKQuarticallyAdmittedKernel_isHS 1)
    (HilbertSchmidt.isHS_hsPow routeKQuarticallyAdmittedKernel_isHS 1)]
  rw [HilbertSchmidt.toOperator_hsPow routeKQuarticallyAdmittedKernel_isHS 1,
    routeKQuarticallyAdmittedKernel_toOperator]
  congr 1

/-- The cubic Hilbert--Schmidt trace is the ordinary cubic trace of the literal carrier. -/
theorem routeKQuarticallyAdmittedKernel_cube_trace :
    (∑' p : Nat.Primes,
      HilbertSchmidt.hsPow routeKQuarticallyAdmittedKernel 2 (p, p)) =
      ContinuousLinearMap.opTrace (routeKQuarticallyAdmittedOperator ^ (3 : ℕ)) := by
  rw [show HilbertSchmidt.hsPow routeKQuarticallyAdmittedKernel 2 =
      HilbertSchmidt.hsComp routeKQuarticallyAdmittedKernel
        (HilbertSchmidt.hsPow routeKQuarticallyAdmittedKernel 1) by rfl]
  rw [← HilbertSchmidt.opTrace_toOperator_comp
    routeKQuarticallyAdmittedKernel_isHS
    (HilbertSchmidt.isHS_hsPow routeKQuarticallyAdmittedKernel_isHS 1)]
  rw [HilbertSchmidt.toOperator_hsPow routeKQuarticallyAdmittedKernel_isHS 1,
    routeKQuarticallyAdmittedKernel_toOperator]
  congr 1


noncomputable def routeKQuarticallyAdmittedEntireDet : ℂ → ℂ :=
  GaloisForLFunctions.HTGeometry.entireDet2 routeKQuarticallyAdmittedKernel

/-- The quartic K-RVM determinant coefficient is fixed by the actual source's first two moments. -/
theorem taylorCoeff_routeKQuarticallyAdmittedEntireDet_four :
    GaloisForLFunctions.HTGeometry.taylorCoeff
      routeKQuarticallyAdmittedEntireDet 4 =
      (routeKSourceZerothMoment : ℂ) ^ (2 : ℕ) / 32 -
        (routeKSourceFirstMoment : ℂ) / 8 := by
  rw [routeKQuarticallyAdmittedEntireDet,
    GaloisForLFunctions.HTGeometry.taylorCoeff_entireDet2_four
      routeKQuarticallyAdmittedKernel_isHS,
    routeKQuarticallyAdmittedKernel_square_trace,
    routeKQuarticallyAdmittedKernel_fourth_trace]
  have h2 := two_mul_opTrace_sq_routeKQuarticallyAdmittedOperator
  have h4 := two_mul_opTrace_four_routeKQuarticallyAdmittedOperator
  have h2' : ContinuousLinearMap.opTrace (routeKQuarticallyAdmittedOperator ^ (2 : ℕ)) =
      (routeKSourceZerothMoment : ℂ) / 2 := by
    linear_combination h2 / 2
  have h4' : ContinuousLinearMap.opTrace (routeKQuarticallyAdmittedOperator ^ (4 : ℕ)) =
      (routeKSourceFirstMoment : ℂ) / 2 := by
    linear_combination h4 / 2
  rw [h2', h4']
  ring



private theorem routeKQuarticallyAdmittedEntireDet_differentiable :
    Differentiable ℂ routeKQuarticallyAdmittedEntireDet := by
  simpa [routeKQuarticallyAdmittedEntireDet] using
    GaloisForLFunctions.HTGeometry.differentiable_entireDet2
      routeKQuarticallyAdmittedKernel_isHS

private theorem routeKQuarticallyAdmittedEntireDet_zero :
    routeKQuarticallyAdmittedEntireDet 0 = 1 := by
  rw [routeKQuarticallyAdmittedEntireDet]
  exact (GaloisForLFunctions.HTGeometry.isRegularizedDet_entireDet2
    routeKQuarticallyAdmittedKernel_isHS).eq_one_at_zero

private theorem taylorCoeff_routeKQuarticallyAdmittedEntireDet_one :
    GaloisForLFunctions.HTGeometry.taylorCoeff
      routeKQuarticallyAdmittedEntireDet 1 = 0 := by
  rw [routeKQuarticallyAdmittedEntireDet,
    GaloisForLFunctions.HTGeometry.taylorCoeff_entireDet2_eq_detCoeff
      routeKQuarticallyAdmittedKernel_isHS,
    GaloisForLFunctions.HTGeometry.detCoeff_one_eq_zero
      routeKQuarticallyAdmittedKernel_isHS]

/-- The quartic carrier's quadratic determinant coefficient is the half-mass dictated by the
paired prime--archimedean source. -/
theorem taylorCoeff_routeKQuarticallyAdmittedEntireDet_two :
    GaloisForLFunctions.HTGeometry.taylorCoeff
      routeKQuarticallyAdmittedEntireDet 2 =
      -(routeKSourceZerothMoment : ℂ) / 4 := by
  rw [routeKQuarticallyAdmittedEntireDet,
    GaloisForLFunctions.HTGeometry.taylorCoeff_entireDet2_two
      routeKQuarticallyAdmittedKernel_isHS,
    routeKQuarticallyAdmittedKernel_square_trace]
  have h2 := two_mul_opTrace_sq_routeKQuarticallyAdmittedOperator
  linear_combination h2 / (-4)

/-- The literal K-RVM determinant has a nonvanishing odd cubic coefficient. -/
theorem taylorCoeff_routeKQuarticallyAdmittedEntireDet_three :
    GaloisForLFunctions.HTGeometry.taylorCoeff
      routeKQuarticallyAdmittedEntireDet 3 =
      -ContinuousLinearMap.opTrace (routeKQuarticallyAdmittedOperator ^ (3 : ℕ)) / 3 := by
  rw [routeKQuarticallyAdmittedEntireDet,
    GaloisForLFunctions.HTGeometry.taylorCoeff_entireDet2_three
      routeKQuarticallyAdmittedKernel_isHS,
    routeKQuarticallyAdmittedKernel_cube_trace]

/-- The determinant is squared because the certified source carrier has two paired channels.
Squaring retains its zero set and gives the source-normalized local multiplicity. -/
noncomputable def routeKQuarticallyAdmittedSquaredEntireDet : ℂ → ℂ :=
  fun z => routeKQuarticallyAdmittedEntireDet z ^ (2 : ℕ)

/-- The paired determinant has the normalized quadratic source coefficient. -/
theorem taylorCoeff_routeKQuarticallyAdmittedSquaredEntireDet_two :
    GaloisForLFunctions.HTGeometry.taylorCoeff
      routeKQuarticallyAdmittedSquaredEntireDet 2 =
      -(routeKSourceZerothMoment : ℂ) / 2 := by
  change GaloisForLFunctions.HTGeometry.taylorCoeff
    (fun z => routeKQuarticallyAdmittedEntireDet z ^ (2 : ℕ)) 2 = _
  rw [GaloisForLFunctions.HTGeometry.taylorCoeff_sq_two_of_value_one_of_linear_zero
    routeKQuarticallyAdmittedEntireDet_differentiable
    routeKQuarticallyAdmittedEntireDet_zero
    taylorCoeff_routeKQuarticallyAdmittedEntireDet_one,
    taylorCoeff_routeKQuarticallyAdmittedEntireDet_two]
  ring

/-- Pairing channels doubles, rather than cancels, the literal cubic determinant coefficient. -/
theorem taylorCoeff_routeKQuarticallyAdmittedSquaredEntireDet_three :
    GaloisForLFunctions.HTGeometry.taylorCoeff
      routeKQuarticallyAdmittedSquaredEntireDet 3 =
      -(2 * ContinuousLinearMap.opTrace (routeKQuarticallyAdmittedOperator ^ (3 : ℕ))) / 3 := by
  change GaloisForLFunctions.HTGeometry.taylorCoeff
    (fun z => routeKQuarticallyAdmittedEntireDet z ^ (2 : ℕ)) 3 = _
  rw [GaloisForLFunctions.HTGeometry.taylorCoeff_sq_three_of_value_one_of_linear_zero
    routeKQuarticallyAdmittedEntireDet_differentiable
    routeKQuarticallyAdmittedEntireDet_zero
    taylorCoeff_routeKQuarticallyAdmittedEntireDet_one,
    taylorCoeff_routeKQuarticallyAdmittedEntireDet_three]
  ring

/-- The paired literal determinant's cubic Taylor coefficient cannot vanish. -/
theorem taylorCoeff_routeKQuarticallyAdmittedSquaredEntireDet_three_ne_zero :
    GaloisForLFunctions.HTGeometry.taylorCoeff
      routeKQuarticallyAdmittedSquaredEntireDet 3 ≠ 0 := by
  rw [taylorCoeff_routeKQuarticallyAdmittedSquaredEntireDet_three]
  have htwo : (2 : ℂ) ≠ 0 := by norm_num
  have hthree : (3 : ℂ) ≠ 0 := by norm_num
  exact div_ne_zero
    (neg_ne_zero.mpr (mul_ne_zero htwo
      opTrace_routeKQuarticallyAdmittedOperator_cube_ne_zero))
    hthree

/-- The normalized centered Xi function has a zero cubic Taylor coefficient by evenness. -/
theorem taylorCoeff_normalized_XiC_three_eq_zero :
    GaloisForLFunctions.HTGeometry.taylorCoeff
      (fun z : ℂ => XiC z / XiC 0) 3 = 0 := by
  rw [GaloisForLFunctions.HTGeometry.taylorCoeff]
  have heq : (fun z : ℂ => XiC z / XiC 0) =
      fun z => (XiC 0)⁻¹ * XiC z := by
    funext z
    ring
  rw [heq, iteratedDeriv_const_mul_field,
    iteratedDeriv_XiC_odd_zero (by decide), mul_zero]
  ring

/-- The literal paired quartic carrier cannot satisfy the proposed all-order normalized Xi
identity: its cubic coefficient is forced nonzero while Xi's is forced zero. -/
theorem routeKQuarticallyAdmittedSquaredEntireDet_ne_normalized_XiC :
    routeKQuarticallyAdmittedSquaredEntireDet ≠ (fun z : ℂ => XiC z / XiC 0) := by
  intro h
  have hcoeff := congrArg (fun f : ℂ → ℂ =>
    GaloisForLFunctions.HTGeometry.taylorCoeff f 3) h
  rw [taylorCoeff_routeKQuarticallyAdmittedSquaredEntireDet_three,
    taylorCoeff_normalized_XiC_three_eq_zero] at hcoeff
  apply taylorCoeff_routeKQuarticallyAdmittedSquaredEntireDet_three_ne_zero
  rw [taylorCoeff_routeKQuarticallyAdmittedSquaredEntireDet_three]
  exact hcoeff

/-- The paired determinant has the normalized quartic source coefficient. -/
theorem taylorCoeff_routeKQuarticallyAdmittedSquaredEntireDet_four :
    GaloisForLFunctions.HTGeometry.taylorCoeff
      routeKQuarticallyAdmittedSquaredEntireDet 4 =
      (routeKSourceZerothMoment : ℂ) ^ (2 : ℕ) / 8 -
        (routeKSourceFirstMoment : ℂ) / 4 := by
  change GaloisForLFunctions.HTGeometry.taylorCoeff
    (fun z => routeKQuarticallyAdmittedEntireDet z ^ (2 : ℕ)) 4 = _
  rw [GaloisForLFunctions.HTGeometry.taylorCoeff_sq_four_of_value_one_of_linear_zero
    routeKQuarticallyAdmittedEntireDet_differentiable
    routeKQuarticallyAdmittedEntireDet_zero
    taylorCoeff_routeKQuarticallyAdmittedEntireDet_one,
    taylorCoeff_routeKQuarticallyAdmittedEntireDet_four,
    taylorCoeff_routeKQuarticallyAdmittedEntireDet_two]
  ring

/-- The paired determinant and normalized centered Xi have the same quadratic Taylor jet. -/
theorem taylorCoeff_routeKQuarticallyAdmittedSquaredEntireDet_two_eq_normalized_XiC :
    GaloisForLFunctions.HTGeometry.taylorCoeff
      routeKQuarticallyAdmittedSquaredEntireDet 2 =
      deriv (deriv XiC) 0 / XiC 0 / 2 := by
  rw [taylorCoeff_routeKQuarticallyAdmittedSquaredEntireDet_two]
  unfold routeKSourceZerothMoment
  rw [analyticTraceMoments_normalizedPrimeArchSource_zero_eq_Xi_ratio]
  have hXi2 : deriv (deriv XiC) 0 = ((deriv (deriv Xi) 0 : ℝ) : ℂ) := by
    simpa using XiC_secondDeriv_ofReal 0
  have hXi0 : XiC 0 = ((Xi 0 : ℝ) : ℂ) := by
    simpa using XiC_ofReal 0
  rw [hXi2, hXi0]
  have hXi : Xi 0 ≠ 0 := Xi_zero_pos.ne'
  push_cast
  field_simp [hXi]

/-- The paired determinant and normalized centered Xi have the same quartic Taylor jet. -/
theorem taylorCoeff_routeKQuarticallyAdmittedSquaredEntireDet_four_eq_normalized_XiC :
    GaloisForLFunctions.HTGeometry.taylorCoeff
      routeKQuarticallyAdmittedSquaredEntireDet 4 =
      iteratedDeriv 4 XiC 0 / XiC 0 / 24 := by
  rw [taylorCoeff_routeKQuarticallyAdmittedSquaredEntireDet_four,
    normalized_XiC_fourth_jet_eq_source_moments,
    routeKSourceZerothMoment_eq_normalizedPrimeArchMoment,
    routeKSourceFirstMoment_eq_normalizedPrimeArchMoment]

/-- Exact fourth-jet diagnostic for the unsquared quartic K-RVM determinant. -/
theorem normalized_XiC_fourth_jet_sub_four_mul_routeKQuarticallyAdmittedEntireDet_four :
    iteratedDeriv 4 XiC 0 / XiC 0 / 24 -
      4 * GaloisForLFunctions.HTGeometry.taylorCoeff
        routeKQuarticallyAdmittedEntireDet 4 =
      (routeKSourceFirstMoment : ℂ) / 4 := by
  rw [normalized_XiC_fourth_jet_eq_source_moments,
    taylorCoeff_routeKQuarticallyAdmittedEntireDet_four,
    routeKSourceZerothMoment_eq_normalizedPrimeArchMoment,
    routeKSourceFirstMoment_eq_normalizedPrimeArchMoment]
  ring


/-- A single determinant has a strictly positive fourth-jet deficit; the paired
determinant above removes this deficit at degree four. -/
theorem normalized_XiC_fourth_jet_ne_four_mul_routeKQuarticallyAdmittedEntireDet_four :
    iteratedDeriv 4 XiC 0 / XiC 0 / 24 ≠
      4 * GaloisForLFunctions.HTGeometry.taylorCoeff
        routeKQuarticallyAdmittedEntireDet 4 := by
  have hgap :=
    normalized_XiC_fourth_jet_sub_four_mul_routeKQuarticallyAdmittedEntireDet_four
  have hnonzero : (routeKSourceFirstMoment : ℂ) / 4 ≠ 0 :=
    div_ne_zero (Complex.ofReal_ne_zero.mpr routeKSourceFirstMoment_pos.ne') (by norm_num)
  intro heq
  apply hnonzero
  rw [← hgap, heq]
  ring

end KRVMPaired
end

end RHTower
