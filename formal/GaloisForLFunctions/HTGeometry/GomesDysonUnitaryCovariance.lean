import GaloisForLFunctions.HTGeometry.GomesFockExponentialFrame

/-!
Internal-frame covariance of the corpus matrix Dyson recurrence. This applies
Gomes's internal-space geometry (arXiv:2404.10461) and reconstruction from a full
menu of tensors (arXiv:2607.24901v1). Arbitrary matrix changes have an exact Gram
defect; preserving the entire normalized recurrence is equivalent to unitarity.
All classifications quantify arbitrary matrix data and supply no proof premises.
-/
open scoped Matrix BigOperators
noncomputable section
namespace GaloisForLFunctions.HTGeometry

/-- Internal conjugation of an observed matrix by arbitrary frame data. -/
def gomesFockConjugate {d : ℕ} (U X : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ := U*X*Uᴴ

/-- Internal conjugation commutes with adjoints without any invertibility assumption. -/
theorem gomesFockConjugate_adjoint {d : ℕ} (U X : Matrix (Fin d) (Fin d) ℂ) :
    (gomesFockConjugate U X)ᴴ = gomesFockConjugate U Xᴴ := by
  simp [gomesFockConjugate,Matrix.mul_assoc]

/-- Conjugation transports finite observation sums exactly. -/
theorem gomesFockConjugate_sum {d m : ℕ}
    (U : Matrix (Fin d) (Fin d) ℂ) (X : Fin m → Matrix (Fin d) (Fin d) ℂ) :
    gomesFockConjugate U (∑ i, X i) = ∑ i, gomesFockConjugate U (X i) := by
  simp [gomesFockConjugate,Matrix.mul_sum,Matrix.sum_mul]

/-- Multiplication under a general frame change inserts exactly its Gram defect. -/
theorem gomesFockConjugate_mul_defect {d : ℕ} (U X Y : Matrix (Fin d) (Fin d) ℂ) :
    gomesFockConjugate U X * gomesFockConjugate U Y =
      gomesFockConjugate U (X*(Uᴴ*U)*Y) := by
  simp only [gomesFockConjugate,Matrix.mul_assoc]

/-- The original covariance map records two copies of the internal Gram defect. -/
theorem gomesFockConjugate_covariance_defect {d k : ℕ}
    (U : Matrix (Fin d) (Fin d) ℂ) (A : Option (Fin k) → Matrix (Fin d) (Fin d) ℂ)
    (X : Matrix (Fin d) (Fin d) ℂ) :
    matrixSemicircleCovariance (fun i => gomesFockConjugate U (A i)) (gomesFockConjugate U X) =
      gomesFockConjugate U (matrixSemicircleCovariance A ((Uᴴ*U)*X*(Uᴴ*U))) := by
  simp only [matrixSemicircleCovariance,gomesFockConjugate,Matrix.mul_sum,Matrix.sum_mul,
    Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,Matrix.mul_assoc]

/-- The normalized Dyson tensor menu transforms by internal conjugation exactly for unitary frames. -/
theorem gomesDyson_unitary_conjugacy_iff {d k : ℕ} (U : Matrix (Fin d) (Fin d) ℂ) :
    (∀ A : Option (Fin k) → Matrix (Fin d) (Fin d) ℂ, ∀ n,
      matrixDysonFormalCoeff (fun i => gomesFockConjugate U (A i)) n =
        gomesFockConjugate U (matrixDysonFormalCoeff A n)) ↔ Uᴴ*U = 1 := by
  constructor
  · intro h
    have h0 := h 0 0
    have hh : U*Uᴴ = 1 := by
      simpa [matrixDysonFormalCoeff,gomesFockConjugate] using h0.symm
    exact mul_eq_one_comm.mp hh
  · intro hu A n
    have huh : U*Uᴴ = 1 := mul_eq_one_comm.mp hu
    induction n using Nat.strong_induction_on with
    | h n ih =>
      cases n with
      | zero => simp [matrixDysonFormalCoeff,gomesFockConjugate,huh]
      | succ n =>
        rw [matrixDysonFormalCoeff,matrixDysonFormalCoeff,gomesFockConjugate_sum]
        apply Finset.sum_congr rfl
        intro p hp
        rw [ih p p.isLt,ih (n-p) (Nat.lt_succ_of_le (Nat.sub_le n p)),
          gomesFockConjugate_covariance_defect,hu,one_mul,mul_one,gomesFockConjugate_mul_defect,
          hu,mul_one]

end GaloisForLFunctions.HTGeometry
