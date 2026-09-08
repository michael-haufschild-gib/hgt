import GaloisForLFunctions.HTGeometry.CoppoNonlocalNoise
import GaloisForLFunctions.HTGeometry.ConstraintRelativity.PassiveRelationHermitianCrossFibre

/-!
# Correlated baths in the Hermitian correlation space

The anomalous noise of arXiv:2606.25061 is compatible with adjoints. Pairing
conjugate amplitudes therefore gives an actual Hermitian, locally invisible
perturbation of every Hermitian part, including positive matrices `Y * Yᴴ`.
No positivity claim is made for a finite Euler step of this isolated channel.
-/

open Matrix
open scoped Kronecker
noncomputable section
namespace HTGeometry.ConstraintRelativity

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- Taking the adjoint conjugates the two local jump operators. -/
theorem coppoCrossNoise_conjTranspose (A : Matrix m m ℂ) (B : Matrix n n ℂ)
    (X : Matrix (m × n) (m × n) ℂ) :
    (coppoCrossNoise A B X)ᴴ = coppoCrossNoise Aᴴ Bᴴ Xᴴ := by
  simp only [coppoCrossNoise, conjTranspose_add, conjTranspose_sub,
    conjTranspose_mul, conjTranspose_kronecker, conjTranspose_one]
  noncomm_ring

/-- The conjugate-amplitude channel pair commutes with adjoint. -/
theorem coppoHermitianCrossNoise_conjTranspose (z : ℂ)
    (A : Matrix m m ℂ) (B : Matrix n n ℂ) (X : Matrix (m × n) (m × n) ℂ) :
    (coppoHermitianCrossNoise z A B X)ᴴ = coppoHermitianCrossNoise z A B Xᴴ := by
  simp only [coppoHermitianCrossNoise, conjTranspose_add, conjTranspose_smul,
    coppoCrossNoise_conjTranspose, conjTranspose_conjTranspose, star_star]
  abel

/-- Every Gram input produces a self-adjoint correlated perturbation. -/
theorem coppoHermitianCrossNoise_gram_isSelfAdjoint (z : ℂ)
    (A : Matrix m m ℂ) (B : Matrix n n ℂ) (Y : Matrix (m × n) (m × n) ℂ) :
    IsSelfAdjoint (coppoHermitianCrossNoise z A B (Y * Yᴴ)) := by
  change (coppoHermitianCrossNoise z A B (Y * Yᴴ))ᴴ = _
  rw [coppoHermitianCrossNoise_conjTranspose]
  simp

/-- The actual Gram-input channel lands in the existing real Hermitian cross fibre. -/
theorem coppoHermitianCrossNoise_gram_mem_hermitianMatrixCrossFibre (z : ℂ)
    (A : Matrix m m ℂ) (B : Matrix n n ℂ) (Y : Matrix (m × n) (m × n) ℂ) :
    coppoHermitianCrossNoise z A B (Y * Yᴴ) ∈ hermitianMatrixCrossFibre :=
  ⟨coppoHermitianCrossNoise_gram_isSelfAdjoint z A B Y,
    coppoHermitianCrossNoise_mem_matrixCrossFibre z A B (Y * Yᴴ)⟩

/-- Local observables have identically zero Hilbert--Schmidt response to cross noise. -/
theorem coppoCrossNoise_hsInner_local (A P : Matrix m m ℂ) (B Q : Matrix n n ℂ)
    (X : Matrix (m × n) (m × n) ℂ) :
    QuantumAlg.hsInner (coppoCrossNoise A B X) (P ⊗ₖ 1 + 1 ⊗ₖ Q) = 0 := by
  classical
  cases isEmpty_or_nonempty m with
  | inl hm =>
    letI := hm
    simp [QuantumAlg.hsInner_def, Matrix.trace]
  | inr hm =>
    letI := hm
    cases isEmpty_or_nonempty n with
    | inl hn =>
      letI := hn
      simp [QuantumAlg.hsInner_def, Matrix.trace]
    | inr hn =>
      letI := hn
      rw [QuantumAlg.hsInner_add_right]
      have hstar := coppoCrossNoise_partialTraces Aᴴ Bᴴ Xᴴ
      rw [← coppoCrossNoise_conjTranspose] at hstar
      have hleft : QuantumAlg.hsInner (coppoCrossNoise A B X) (P ⊗ₖ 1) = 0 := by
        rw [QuantumAlg.hsInner_def, ← trace_partialTraceRight,
          partialTraceRight_mul_leftLocal, hstar.1]
        simp
      have hright : QuantumAlg.hsInner (coppoCrossNoise A B X) (1 ⊗ₖ Q) = 0 := by
        rw [QuantumAlg.hsInner_def, ← trace_partialTraceLeft,
          partialTraceLeft_mul_rightLocal, hstar.2]
        simp
      rw [hleft, hright, add_zero]

end HTGeometry.ConstraintRelativity
