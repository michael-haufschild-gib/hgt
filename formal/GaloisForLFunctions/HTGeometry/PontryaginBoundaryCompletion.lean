import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Tactic

open Complex Matrix
open scoped Matrix

/-!
# Exact rank-two Pontryagin boundary completion

For a finite matrix whose skew metric defect factors through two boundary channels, this module
constructs an explicit two-channel extension which is self-adjoint for a metric congruent to
`I ⊕ J`.  When `J` is hyperbolic, the extension therefore has one negative direction.  The
construction is algebraic and does not assert spectral or determinant preservation; that is the
separate source-level problem needed for the theta/Xi route.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

def completionY (U : Matrix n (Fin 2) ℂ) (J : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2) n ℂ :=
  (-Complex.I / 2 : ℂ) • J * Uᴴ

def completionQ (U : Matrix n (Fin 2) ℂ) (J : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  Uᴴ * U + J

def completionK (B : Matrix n n ℂ) (U : Matrix n (Fin 2) ℂ) (J : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  Uᴴ * B * U - Uᴴ * Bᴴ * U +
    completionQ U J * completionY U J * U -
      Uᴴ * (completionY U J)ᴴ * completionQ U J

def completionZ (B : Matrix n n ℂ) (U : Matrix n (Fin 2) ℂ) (J : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 2 : ℂ) • (J * completionK B U J)

def completionX (B : Matrix n n ℂ) (U : Matrix n (Fin 2) ℂ) (J : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix n (Fin 2) ℂ :=
  Bᴴ * U + (completionY U J)ᴴ * completionQ U J - U * completionZ B U J

def completionOperator (B : Matrix n n ℂ) (U : Matrix n (Fin 2) ℂ) (J : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (n ⊕ Fin 2) (n ⊕ Fin 2) ℂ :=
  Matrix.fromBlocks B (completionX B U J) (completionY U J) (completionZ B U J)

def completionMetric (U : Matrix n (Fin 2) ℂ) (J : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (n ⊕ Fin 2) (n ⊕ Fin 2) ℂ :=
  Matrix.fromBlocks 1 U Uᴴ (completionQ U J)

/-- The finite-rank shear which exposes the metric's Pontryagin congruence. -/
def completionShear (U : Matrix n (Fin 2) ℂ) :
    Matrix (n ⊕ Fin 2) (n ⊕ Fin 2) ℂ :=
  Matrix.fromBlocks 1 U 0 1

/-- Diagonal Hilbert-plus-boundary metric. -/
def completionDiagonalMetric (J : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (n ⊕ Fin 2) (n ⊕ Fin 2) ℂ :=
  Matrix.fromBlocks 1 0 0 J

/-- The completion metric is congruent to its positive carrier plus the two-channel boundary
form.  Thus a hyperbolic `J` gives exactly one negative metric direction. -/
theorem completionMetric_eq_congruence
    (U : Matrix n (Fin 2) ℂ) (J : Matrix (Fin 2) (Fin 2) ℂ) :
    completionMetric U J =
      (completionShear U)ᴴ * completionDiagonalMetric J * completionShear U := by
  rw [completionMetric, completionShear, completionDiagonalMetric,
    Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.one_apply, completionQ]

theorem completion_metric_adjoint
    (B : Matrix n n ℂ) (U : Matrix n (Fin 2) ℂ) (J : Matrix (Fin 2) (Fin 2) ℂ)
    (hB : B - Bᴴ = (completionY U J)ᴴ * Uᴴ - U * completionY U J)
    (hJ : Jᴴ = J) (hJ_sq : J * J = 1) :
    completionMetric U J * completionOperator B U J =
      (completionOperator B U J)ᴴ * completionMetric U J := by
  have hQstar : (completionQ U J)ᴴ = completionQ U J := by
    simp only [completionQ, Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hJ]
  have hKstar : (completionK B U J)ᴴ = -completionK B U J := by
    have hA : (Uᴴ * B * U)ᴴ = Uᴴ * Bᴴ * U := by
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      rw [← Matrix.mul_assoc]
    have hD : (completionQ U J * completionY U J * U)ᴴ =
        Uᴴ * (completionY U J)ᴴ * completionQ U J := by
      simp only [Matrix.conjTranspose_mul, hQstar]
      exact (Matrix.mul_assoc _ _ _).symm
    have hrepr : completionK B U J =
        (Uᴴ * B * U + completionQ U J * completionY U J * U) -
          (Uᴴ * B * U + completionQ U J * completionY U J * U)ᴴ := by
      rw [Matrix.conjTranspose_add, hA, hD]
      unfold completionK
      module
    rw [hrepr, Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose]
    module
  have hZcomm :
      J * completionZ B U J - (completionZ B U J)ᴴ * J = completionK B U J := by
    have hhalf : star (1 / 2 : ℂ) = (1 / 2 : ℂ) := by norm_num
    unfold completionZ
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, hJ, hKstar, hhalf]
    calc
      J * ((1 / 2 : ℂ) • (J * completionK B U J)) -
          ((1 / 2 : ℂ) • ((-completionK B U J) * J)) * J =
          (1 / 2 : ℂ) • (J * (J * completionK B U J)) -
            (1 / 2 : ℂ) • (((-completionK B U J) * J) * J) := by
              rw [Matrix.mul_smul, Matrix.smul_mul]
      _ = (1 / 2 : ℂ) •
            (completionK B U J - (-completionK B U J)) := by
              rw [← Matrix.mul_assoc, hJ_sq, Matrix.one_mul,
                Matrix.mul_assoc, hJ_sq, Matrix.mul_one]
              module
      _ = completionK B U J := by module
  have hXstar : (completionX B U J)ᴴ =
      Uᴴ * B + completionQ U J * completionY U J -
        (completionZ B U J)ᴴ * Uᴴ := by
    simp only [completionX, Matrix.conjTranspose_sub, Matrix.conjTranspose_add,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hQstar]
  have h12 : completionX B U J + U * completionZ B U J =
      Bᴴ * U + (completionY U J)ᴴ * completionQ U J := by
    unfold completionX
    module
  have h21 : Uᴴ * B + completionQ U J * completionY U J =
      (completionX B U J)ᴴ + (completionZ B U J)ᴴ * Uᴴ := by
    rw [hXstar]
    module
  have h22 : Uᴴ * completionX B U J + completionQ U J * completionZ B U J =
      (completionX B U J)ᴴ * U + (completionZ B U J)ᴴ * completionQ U J := by
    rw [hXstar]
    have hsplit :
        Uᴴ * completionX B U J + completionQ U J * completionZ B U J -
          ((Uᴴ * B + completionQ U J * completionY U J -
            (completionZ B U J)ᴴ * Uᴴ) * U +
            (completionZ B U J)ᴴ * completionQ U J) =
          -completionK B U J +
            (completionQ U J - Uᴴ * U) * completionZ B U J -
              (completionZ B U J)ᴴ * (completionQ U J - Uᴴ * U) := by
      unfold completionX completionK
      simp only [Matrix.mul_sub, Matrix.mul_add, Matrix.sub_mul,
        Matrix.add_mul, ← Matrix.mul_assoc]
      module
    apply sub_eq_zero.mp
    rw [hsplit]
    have hQsub : completionQ U J - Uᴴ * U = J := by
      unfold completionQ
      module
    rw [hQsub]
    calc
      -completionK B U J + J * completionZ B U J -
          (completionZ B U J)ᴴ * J =
          -completionK B U J +
            (J * completionZ B U J - (completionZ B U J)ᴴ * J) := by module
      _ = 0 := by rw [hZcomm]; module
  rw [completionMetric, completionOperator,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_conjTranspose,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj]
  constructor
  · simp only [Matrix.one_mul, Matrix.mul_one]
    calc
      B + U * completionY U J =
          (B - Bᴴ) + (Bᴴ + U * completionY U J) := by module
      _ = ((completionY U J)ᴴ * Uᴴ - U * completionY U J) +
          (Bᴴ + U * completionY U J) := by rw [hB]
      _ = Bᴴ + (completionY U J)ᴴ * Uᴴ := by module
  constructor
  · simpa only [Matrix.one_mul] using h12
  constructor
  · simpa only [Matrix.mul_one] using h21
  · exact h22

end

end HTGeometry
