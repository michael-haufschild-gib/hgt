import GaloisForLFunctions.HTGeometry.ConstraintRelativity.BipartiteMatrixDecomposition
import GaloisForLFunctions.HTGeometry.RydbergProjectorDephasing

/-!
# Locally invisible correlated noise

The cross-bath term of Coppo et al., arXiv:2606.25061, Eq. (4), is a negative
mixed commutator for commuting local embeddings. Its range lies in the existing
bipartite cross fibre, without any assumption on the joint matrix or jump operators.
-/

open Matrix
open scoped Kronecker

noncomputable section
namespace HTGeometry.ConstraintRelativity

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- One anomalous cross-bath noise term, before adding its adjoint channel. -/
def coppoCrossNoise (A : Matrix m m ℂ) (B : Matrix n n ℂ)
    (X : Matrix (m × n) (m × n) ℂ) : Matrix (m × n) (m × n) ℂ :=
  (A ⊗ₖ 1) * X * (1 ⊗ₖ B) + (1 ⊗ₖ B) * X * (A ⊗ₖ 1) -
    ((A ⊗ₖ B) * X + X * (A ⊗ₖ B))

/-- The anomalous cross channel is the negative mixed commutator. -/
theorem coppoCrossNoise_eq_mixedCommutator (A : Matrix m m ℂ) (B : Matrix n n ℂ)
    (X : Matrix (m × n) (m × n) ℂ) :
    coppoCrossNoise A B X =
      -matrixCommutator (matrixCommutator X (1 ⊗ₖ B)) (A ⊗ₖ 1) := by
  have hab : (A ⊗ₖ (1 : Matrix n n ℂ)) * (1 ⊗ₖ B) = A ⊗ₖ B := by
    rw [← Matrix.mul_kronecker_mul]; simp
  have hba : ((1 : Matrix m m ℂ) ⊗ₖ B) * (A ⊗ₖ 1) = A ⊗ₖ B := by
    rw [← Matrix.mul_kronecker_mul]; simp
  dsimp [coppoCrossNoise, matrixCommutator]
  noncomm_ring [hab, hba]
  simp only [← Matrix.mul_assoc, hab]
  abel

/-- Cross-bath noise changes neither reduced matrix, even for entangled inputs. -/
theorem coppoCrossNoise_partialTraces (A : Matrix m m ℂ) (B : Matrix n n ℂ)
    (X : Matrix (m × n) (m × n) ℂ) :
    partialTraceRight (coppoCrossNoise A B X) = 0 ∧
      partialTraceLeft (coppoCrossNoise A B X) = 0 := by
  classical
  cases isEmpty_or_nonempty m with
  | inl hm =>
    letI := hm
    constructor
    · exact Subsingleton.elim _ _
    · ext i j; simp [partialTraceLeft]
  | inr hm =>
    letI := hm
    cases isEmpty_or_nonempty n with
    | inl hn =>
      letI := hn
      constructor
      · ext i j; simp [partialTraceRight]
      · exact Subsingleton.elim _ _
    | inr hn =>
      letI := hn
      rw [coppoCrossNoise_eq_mixedCommutator]
      have hnegR (Y : Matrix (m × n) (m × n) ℂ) :
          partialTraceRight (-Y) = -partialTraceRight Y := by
        exact partialTraceRightLinear.map_neg Y
      have hnegL (Y : Matrix (m × n) (m × n) ℂ) :
          partialTraceLeft (-Y) = -partialTraceLeft Y := by
        exact partialTraceLeftLinear.map_neg Y
      rw [hnegR, hnegL, partialTraceLeft_commutator_leftLocal]
      constructor
      · rw [matrixCommutator, partialTraceRight_sub,
          partialTraceRight_mul_leftLocal, partialTraceRight_leftLocal_mul,
          partialTraceRight_commutator_rightLocal]
        simp
      · simp

/-- The paper's noise term belongs to the corpus's invisible cross fibre. -/
theorem coppoCrossNoise_mem_matrixCrossFibre (A : Matrix m m ℂ) (B : Matrix n n ℂ)
    (X : Matrix (m × n) (m × n) ℂ) :
    coppoCrossNoise A B X ∈ matrixCrossFibre :=
  coppoCrossNoise_partialTraces A B X

/-- Cross-bath noise preserves the joint trace. -/
theorem trace_coppoCrossNoise (A : Matrix m m ℂ) (B : Matrix n n ℂ)
    (X : Matrix (m × n) (m × n) ℂ) :
    (coppoCrossNoise A B X).trace = 0 := by
  rw [← trace_partialTraceRight, (coppoCrossNoise_partialTraces A B X).1,
    Matrix.trace_zero]

/-- On product inputs, the noise factors into the product of local commutators. -/
theorem coppoCrossNoise_kronecker (A P : Matrix m m ℂ) (B Q : Matrix n n ℂ) :
    coppoCrossNoise A B (P ⊗ₖ Q) = -(A * P - P * A) ⊗ₖ (B * Q - Q * B) := by
  simp only [coppoCrossNoise, ← Matrix.mul_kronecker_mul, mul_one, one_mul,
    ]
  ext i j
  simp only [Matrix.kroneckerMap_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply]
  ring

/-- Symmetric and antisymmetric collective jump operators obey a parallelogram law. -/
theorem coppoLindblad_parallelogram {d : ℕ} (L M X : RHTower.QuantumMatrix d) :
    RHTower.finiteLindbladDissipator (L + M) X +
      RHTower.finiteLindbladDissipator (L - M) X =
      2 • RHTower.finiteLindbladDissipator L X +
        2 • RHTower.finiteLindbladDissipator M X := by
  simp only [RHTower.finiteLindbladDissipator, RHTower.finiteLindbladGain,
    RHTower.finiteLindbladDrain, Matrix.conjTranspose_add, Matrix.conjTranspose_sub,
    add_mul, mul_add, sub_mul, mul_sub, smul_add, smul_sub]
  module

/-- Add a channel and its adjoint with conjugate amplitudes. -/
def coppoHermitianCrossNoise (z : ℂ) (A : Matrix m m ℂ) (B : Matrix n n ℂ)
    (X : Matrix (m × n) (m × n) ℂ) : Matrix (m × n) (m × n) ℂ :=
  z • coppoCrossNoise A B X + star z • coppoCrossNoise Aᴴ Bᴴ X

/-- The full pair of anomalous channels is also locally invisible. -/
theorem coppoHermitianCrossNoise_mem_matrixCrossFibre (z : ℂ)
    (A : Matrix m m ℂ) (B : Matrix n n ℂ) (X : Matrix (m × n) (m × n) ℂ) :
    coppoHermitianCrossNoise z A B X ∈ matrixCrossFibre :=
  matrixCrossFibre.add_mem
    (matrixCrossFibre.smul_mem z (coppoCrossNoise_mem_matrixCrossFibre A B X))
    (matrixCrossFibre.smul_mem (star z) (coppoCrossNoise_mem_matrixCrossFibre Aᴴ Bᴴ X))

/-- A complete correlated kick preserves both local observations for arbitrary strength. -/
theorem coppoHermitianCrossNoise_local_invariance (z : ℂ)
    (A : Matrix m m ℂ) (B : Matrix n n ℂ) (X : Matrix (m × n) (m × n) ℂ) :
    partialTraceRight (X + coppoHermitianCrossNoise z A B X) = partialTraceRight X ∧
      partialTraceLeft (X + coppoHermitianCrossNoise z A B X) = partialTraceLeft X := by
  have h := coppoHermitianCrossNoise_mem_matrixCrossFibre z A B X
  rw [mem_matrixCrossFibre] at h
  simp [h.1, h.2]

/-- Arbitrary finite channel superpositions remain invisible to both observers. -/
theorem coppoCrossNoise_sum_mem_matrixCrossFibre {ι : Type*}
    (s : Finset ι) (z : ι → ℂ) (A : ι → Matrix m m ℂ) (B : ι → Matrix n n ℂ)
    (X : Matrix (m × n) (m × n) ℂ) :
    (∑ i ∈ s, z i • coppoCrossNoise (A i) (B i) X) ∈ matrixCrossFibre := by
  exact matrixCrossFibre.sum_mem fun i _ =>
    matrixCrossFibre.smul_mem _ (coppoCrossNoise_mem_matrixCrossFibre _ _ _)

end HTGeometry.ConstraintRelativity
