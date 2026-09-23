import GaloisForLFunctions.HTGeometry.PrimitiveRecordPolaritySelector

/-!
# Ordered source pairing generates a complex structure

The retained/created source polarity `J = diag(1, -1)` and the source-selected paired record
`S = [[0, 1], [1, 0]]` are involutions that anticommute. Their ordered product therefore squares
to `-1`. A scalar paired transfer `b • S` has ordered square `-(b ^ (2 : ℕ)) • 1`.

This is the standard graded real Clifford-algebra bridge `Cl(2,0) ≃ M₂(ℝ)`. The formal statements do not
derive central complex scalars, a Hilbert space, positivity, quantum probability, time, spacetime,
gravity, or gauge forces.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open scoped Matrix

variable {K : Type*} [Field K]

/-- Ordered product of retained/created source polarity and paired composition. Over `ℝ`, this is
the standard complex structure on the two-dimensional real carrier. -/
def sourceOrderedPairComplexStructure : Matrix (Fin 2) (Fin 2) K :=
  recordPolarityMatrix * pairRecordMatrix

/-- Source polarity is an involution. -/
theorem recordPolarityMatrix_mul_self :
    (recordPolarityMatrix : Matrix (Fin 2) (Fin 2) K) *
      recordPolarityMatrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [recordPolarityMatrix, Matrix.mul_apply, Fin.sum_univ_two]

/-- Paired composition is an involution over every field. -/
theorem pairRecordMatrix_mul_self :
    (pairRecordMatrix : Matrix (Fin 2) (Fin 2) K) *
      pairRecordMatrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pairRecordMatrix, Matrix.mul_apply, Fin.sum_univ_two]

/-- Source polarity and paired composition anticommute. -/
theorem recordPolarity_pair_anticommute :
    (recordPolarityMatrix : Matrix (Fin 2) (Fin 2) K) *
      pairRecordMatrix =
        -(pairRecordMatrix * recordPolarityMatrix) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [recordPolarityMatrix, pairRecordMatrix, Matrix.mul_apply,
      Fin.sum_univ_two]

/-- **Ordered-pair complex-structure law.** The ordered product of the two source involutions
squares to minus the identity. -/
theorem sourceOrderedPairComplexStructure_sq :
    (sourceOrderedPairComplexStructure :
      Matrix (Fin 2) (Fin 2) K) *
        sourceOrderedPairComplexStructure = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sourceOrderedPairComplexStructure, recordPolarityMatrix,
      pairRecordMatrix, Matrix.mul_apply, Fin.sum_univ_two]

/-- Reversing source order reverses the generated complex structure. -/
theorem pair_recordPolarity_eq_neg_sourceOrderedPair :
    (pairRecordMatrix : Matrix (Fin 2) (Fin 2) K) *
      recordPolarityMatrix =
        -sourceOrderedPairComplexStructure := by
  rw [sourceOrderedPairComplexStructure, recordPolarity_pair_anticommute]
  simp

/-- A scalar paired transfer has ordered square equal to minus its scalar square times the unit. -/
theorem sourceOrderedScaledPair_sq (b : K) :
    (recordPolarityMatrix * (b • pairRecordMatrix) :
      Matrix (Fin 2) (Fin 2) K) *
        (recordPolarityMatrix * (b • pairRecordMatrix)) =
      -(b ^ (2 : ℕ)) • (1 : Matrix (Fin 2) (Fin 2) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [recordPolarityMatrix, pairRecordMatrix, Matrix.mul_apply,
      Fin.sum_univ_two, pow_two]

/-- Every symmetric transfer odd under source polarity has the ordered square forced by its unique
paired coefficient. -/
theorem oddSymmetricRecord_ordered_sq
    [CharZero K]
    (q : Matrix (Fin 2) (Fin 2) K)
    (hsymm : qᵀ = q)
    (hodd : recordPolarityMatrixᵀ * q * recordPolarityMatrix = -q) :
    (recordPolarityMatrix * q) * (recordPolarityMatrix * q) =
      -(q 0 1 ^ (2 : ℕ)) • (1 : Matrix (Fin 2) (Fin 2) K) := by
  rw [odd_symmetric_record_eq_smul_pair q hsymm hodd]
  simpa [pairRecordMatrix] using sourceOrderedScaledPair_sq (q 0 1)

/-- Matrix representing the scalar pair `(a, b)` relative to the generated complex structure:
`a • 1 + b • 𝓘`. -/
def sourceComplexScalar (a b : K) : Matrix (Fin 2) (Fin 2) K :=
  a • 1 + b • sourceOrderedPairComplexStructure

/-- Generated scalar matrices obey the usual complex multiplication rule. -/
theorem sourceComplexScalar_mul (a b c d : K) :
    sourceComplexScalar a b * sourceComplexScalar c d =
      sourceComplexScalar (a * c - b * d) (a * d + b * c) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sourceComplexScalar, sourceOrderedPairComplexStructure,
      recordPolarityMatrix, pairRecordMatrix, Matrix.mul_apply,
      Fin.sum_univ_two]
  all_goals ring

/-- Generated scalar matrices commute. -/
theorem sourceComplexScalar_commute (a b c d : K) :
    sourceComplexScalar a b * sourceComplexScalar c d =
      sourceComplexScalar c d * sourceComplexScalar a b := by
  rw [sourceComplexScalar_mul, sourceComplexScalar_mul]
  congr 1 <;> ring

/-- The two scalar coordinates are uniquely represented by their generated scalar matrix. -/
theorem sourceComplexScalar_pair_injective :
    Function.Injective
      (fun p : K × K => sourceComplexScalar p.1 p.2) := by
  intro p q hpq
  apply Prod.ext
  · have h00 := congrArg
      (fun M : Matrix (Fin 2) (Fin 2) K => M 0 0) hpq
    simpa [sourceComplexScalar, sourceOrderedPairComplexStructure,
      recordPolarityMatrix, pairRecordMatrix] using h00
  · have h01 := congrArg
      (fun M : Matrix (Fin 2) (Fin 2) K => M 0 1) hpq
    simpa [sourceComplexScalar, sourceOrderedPairComplexStructure,
      recordPolarityMatrix, pairRecordMatrix] using h01

/-- **Generated-complex centralizer law.** A matrix commutes with the ordered source-pair complex
structure exactly when it is a unique generated scalar `a • 1 + b • 𝓘`. -/
theorem commutes_sourceOrderedPair_iff (A : Matrix (Fin 2) (Fin 2) K) :
    A * sourceOrderedPairComplexStructure =
        sourceOrderedPairComplexStructure * A ↔
      ∃ a b : K, A = sourceComplexScalar a b := by
  constructor
  · intro h
    have h00 := congrArg
      (fun M : Matrix (Fin 2) (Fin 2) K => M 0 0) h
    have h01 := congrArg
      (fun M : Matrix (Fin 2) (Fin 2) K => M 0 1) h
    refine ⟨A 0 0, A 0 1, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j
    · simp [sourceComplexScalar, sourceOrderedPairComplexStructure,
        recordPolarityMatrix, pairRecordMatrix]
    · simp [sourceComplexScalar, sourceOrderedPairComplexStructure,
        recordPolarityMatrix, pairRecordMatrix]
    · simpa [sourceOrderedPairComplexStructure, recordPolarityMatrix,
        pairRecordMatrix, Matrix.mul_apply, Fin.sum_univ_two,
        sourceComplexScalar] using h00.symm
    · simpa [sourceOrderedPairComplexStructure, recordPolarityMatrix,
        pairRecordMatrix, Matrix.mul_apply, Fin.sum_univ_two,
        sourceComplexScalar] using h01.symm
  · rintro ⟨a, b, rfl⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [sourceComplexScalar, sourceOrderedPairComplexStructure,
        recordPolarityMatrix, pairRecordMatrix, Matrix.mul_apply,
        Fin.sum_univ_two]

/-- Simultaneous reversal of the two real source generators, written entrywise. -/
def sourcePairParity (A : Matrix (Fin 2) (Fin 2) K) :
    Matrix (Fin 2) (Fin 2) K :=
  !![A 1 1, -A 1 0; -A 0 1, A 0 0]

/-- Source-pair parity is conjugation by the ordered-pair complex structure. -/
theorem sourcePairParity_eq_conjugation
    (A : Matrix (Fin 2) (Fin 2) K) :
    sourcePairParity A =
      -(sourceOrderedPairComplexStructure * A *
        sourceOrderedPairComplexStructure) := by
  have hK :
      (sourceOrderedPairComplexStructure :
        Matrix (Fin 2) (Fin 2) K) = !![0, 1; -1, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [sourceOrderedPairComplexStructure, recordPolarityMatrix,
        pairRecordMatrix, Matrix.mul_apply, Fin.sum_univ_two]
  rw [Matrix.mul_assoc, hK]
  have hRight := Matrix.two_mul_expl A
    (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) K)
  have hBoth := Matrix.two_mul_expl
    (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) K)
    (A * !![0, 1; -1, 0])
  rcases hRight with ⟨hR00, hR01, hR10, hR11⟩
  rcases hBoth with ⟨hB00, hB01, hB10, hB11⟩
  simp at hR00 hR01 hR10 hR11 hB00 hB01 hB10 hB11
  ext i j
  fin_cases i <;> fin_cases j
  · simp [sourcePairParity]
    rw [hB00, hR10]
    simp
  · simp [sourcePairParity]
    rw [hB01, hR11]
  · simp [sourcePairParity]
    rw [hB10, hR00]
    simp
  · simp [sourcePairParity]
    rw [hB11, hR01]
    simp

/-- Source-pair parity is an involution. -/
theorem sourcePairParity_involutive :
    Function.Involutive
      (sourcePairParity :
        Matrix (Fin 2) (Fin 2) K → Matrix (Fin 2) (Fin 2) K) := by
  intro A
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sourcePairParity]

/-- Source-pair parity preserves matrix multiplication. -/
theorem sourcePairParity_mul
    (A B : Matrix (Fin 2) (Fin 2) K) :
    sourcePairParity (A * B) =
      sourcePairParity A * sourcePairParity B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sourcePairParity, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals ring

/-- Source-pair parity reverses the record-polarity generator. -/
@[simp]
theorem sourcePairParity_recordPolarity :
    sourcePairParity (recordPolarityMatrix :
      Matrix (Fin 2) (Fin 2) K) = -recordPolarityMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sourcePairParity, recordPolarityMatrix]

/-- Source-pair parity reverses the paired-record generator. -/
@[simp]
theorem sourcePairParity_pairRecord :
    sourcePairParity (pairRecordMatrix :
      Matrix (Fin 2) (Fin 2) K) = -pairRecordMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sourcePairParity, pairRecordMatrix]

/-- **Source-neutral fixed-algebra law.** The parity-fixed matrices are exactly the generated
complex scalar matrices. -/
theorem sourcePairParity_fixed_iff_complexScalar
    (A : Matrix (Fin 2) (Fin 2) K) :
    sourcePairParity A = A ↔
      ∃ a b : K, A = sourceComplexScalar a b := by
  constructor
  · intro h
    have h00 := congrArg
      (fun M : Matrix (Fin 2) (Fin 2) K => M 0 0) h
    have h01 := congrArg
      (fun M : Matrix (Fin 2) (Fin 2) K => M 0 1) h
    simp [sourcePairParity] at h00 h01
    refine ⟨A 0 0, A 0 1, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j
    · simp [sourceComplexScalar, sourceOrderedPairComplexStructure,
        recordPolarityMatrix, pairRecordMatrix]
    · simp [sourceComplexScalar, sourceOrderedPairComplexStructure,
        recordPolarityMatrix, pairRecordMatrix]
    · simpa [sourceComplexScalar, sourceOrderedPairComplexStructure,
        recordPolarityMatrix, pairRecordMatrix] using
        congrArg Neg.neg h01
    · simpa [sourceComplexScalar, sourceOrderedPairComplexStructure,
        recordPolarityMatrix, pairRecordMatrix] using h00
  · rintro ⟨a, b, rfl⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [sourcePairParity, sourceComplexScalar,
        sourceOrderedPairComplexStructure, recordPolarityMatrix,
        pairRecordMatrix]

/-- Source-pair parity fixes exactly the centralizer of the ordered-pair complex structure. -/
theorem sourcePairParity_fixed_iff_commutes
    (A : Matrix (Fin 2) (Fin 2) K) :
    sourcePairParity A = A ↔
      A * sourceOrderedPairComplexStructure =
        sourceOrderedPairComplexStructure * A := by
  constructor
  · intro h
    exact (commutes_sourceOrderedPair_iff A).mpr
      ((sourcePairParity_fixed_iff_complexScalar A).mp h)
  · intro h
    exact (sourcePairParity_fixed_iff_complexScalar A).mpr
      ((commutes_sourceOrderedPair_iff A).mp h)

/-- Conjugation by the record-polarity generator: reverse the paired generator while retaining
record polarity. -/
def recordSourceReversal (A : Matrix (Fin 2) (Fin 2) K) :
    Matrix (Fin 2) (Fin 2) K :=
  recordPolarityMatrix * A * recordPolarityMatrix

/-- Conjugation by the paired-record generator: reverse record polarity while retaining the paired
generator. -/
def pairSourceReversal (A : Matrix (Fin 2) (Fin 2) K) :
    Matrix (Fin 2) (Fin 2) K :=
  pairRecordMatrix * A * pairRecordMatrix

/-- Record-source reversal is involutive. -/
theorem recordSourceReversal_involutive :
    Function.Involutive
      (recordSourceReversal :
        Matrix (Fin 2) (Fin 2) K → Matrix (Fin 2) (Fin 2) K) := by
  intro A
  calc
    recordSourceReversal (recordSourceReversal A) =
        (recordPolarityMatrix * recordPolarityMatrix) * A *
          (recordPolarityMatrix * recordPolarityMatrix) := by
      simp only [recordSourceReversal]
      ac_rfl
    _ = A := by rw [recordPolarityMatrix_mul_self]; simp

/-- Paired-source reversal is involutive. -/
theorem pairSourceReversal_involutive :
    Function.Involutive
      (pairSourceReversal :
        Matrix (Fin 2) (Fin 2) K → Matrix (Fin 2) (Fin 2) K) := by
  intro A
  calc
    pairSourceReversal (pairSourceReversal A) =
        (pairRecordMatrix * pairRecordMatrix) * A *
          (pairRecordMatrix * pairRecordMatrix) := by
      simp only [pairSourceReversal]
      ac_rfl
    _ = A := by rw [pairRecordMatrix_mul_self]; simp

/-- Record-source reversal preserves multiplication. -/
theorem recordSourceReversal_mul
    (A B : Matrix (Fin 2) (Fin 2) K) :
    recordSourceReversal (A * B) =
      recordSourceReversal A * recordSourceReversal B := by
  calc
    recordSourceReversal (A * B) =
        recordPolarityMatrix * A * B * recordPolarityMatrix := by
      simp only [recordSourceReversal]
      ac_rfl
    _ = recordPolarityMatrix * A *
          (recordPolarityMatrix * recordPolarityMatrix) * B *
            recordPolarityMatrix := by
      rw [recordPolarityMatrix_mul_self]
      simp
    _ = recordSourceReversal A * recordSourceReversal B := by
      simp only [recordSourceReversal]
      ac_rfl

/-- Paired-source reversal preserves multiplication. -/
theorem pairSourceReversal_mul
    (A B : Matrix (Fin 2) (Fin 2) K) :
    pairSourceReversal (A * B) =
      pairSourceReversal A * pairSourceReversal B := by
  calc
    pairSourceReversal (A * B) =
        pairRecordMatrix * A * B * pairRecordMatrix := by
      simp only [pairSourceReversal]
      ac_rfl
    _ = pairRecordMatrix * A * (pairRecordMatrix * pairRecordMatrix) *
          B * pairRecordMatrix := by
      rw [pairRecordMatrix_mul_self]
      simp
    _ = pairSourceReversal A * pairSourceReversal B := by
      simp only [pairSourceReversal]
      ac_rfl

/-- Reversing the paired source and then the record source is simultaneous source-pair parity. -/
theorem record_pair_sourceReversal_eq_sourcePairParity
    (A : Matrix (Fin 2) (Fin 2) K) :
    recordSourceReversal (pairSourceReversal A) =
      sourcePairParity A := by
  rw [sourcePairParity_eq_conjugation]
  calc
    recordSourceReversal (pairSourceReversal A) =
        (recordPolarityMatrix * pairRecordMatrix) * A *
          (pairRecordMatrix * recordPolarityMatrix) := by
      simp only [recordSourceReversal, pairSourceReversal]
      ac_rfl
    _ = sourceOrderedPairComplexStructure * A *
          (-sourceOrderedPairComplexStructure) := by
      rw [pair_recordPolarity_eq_neg_sourceOrderedPair]
      rfl
    _ = -(sourceOrderedPairComplexStructure * A *
          sourceOrderedPairComplexStructure) := by simp

/-- The two individual source reversals commute: the reverse order gives the same simultaneous
source-pair parity. -/
theorem pair_record_sourceReversal_eq_sourcePairParity
    (A : Matrix (Fin 2) (Fin 2) K) :
    pairSourceReversal (recordSourceReversal A) =
      sourcePairParity A := by
  rw [sourcePairParity_eq_conjugation]
  calc
    pairSourceReversal (recordSourceReversal A) =
        (pairRecordMatrix * recordPolarityMatrix) * A *
          (recordPolarityMatrix * pairRecordMatrix) := by
      simp only [recordSourceReversal, pairSourceReversal]
      ac_rfl
    _ = (-sourceOrderedPairComplexStructure) * A *
          sourceOrderedPairComplexStructure := by
      rw [pair_recordPolarity_eq_neg_sourceOrderedPair]
      rfl
    _ = -(sourceOrderedPairComplexStructure * A *
          sourceOrderedPairComplexStructure) := by simp

/-- Each individual source reversal negates the ordered-pair complex direction. -/
@[simp]
theorem recordSourceReversal_sourceOrderedPair :
    recordSourceReversal
      (sourceOrderedPairComplexStructure :
        Matrix (Fin 2) (Fin 2) K) =
      -sourceOrderedPairComplexStructure := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [recordSourceReversal, sourceOrderedPairComplexStructure,
      recordPolarityMatrix, pairRecordMatrix, Matrix.mul_apply,
      Fin.sum_univ_two]

/-- Each individual source reversal negates the ordered-pair complex direction. -/
@[simp]
theorem pairSourceReversal_sourceOrderedPair :
    pairSourceReversal
      (sourceOrderedPairComplexStructure :
        Matrix (Fin 2) (Fin 2) K) =
      -sourceOrderedPairComplexStructure := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pairSourceReversal, sourceOrderedPairComplexStructure,
      recordPolarityMatrix, pairRecordMatrix, Matrix.mul_apply,
      Fin.sum_univ_two]

@[simp]
theorem recordSourceReversal_add
    (A B : Matrix (Fin 2) (Fin 2) K) :
    recordSourceReversal (A + B) =
      recordSourceReversal A + recordSourceReversal B := by
  simp [recordSourceReversal, mul_add, add_mul]

@[simp]
theorem pairSourceReversal_add
    (A B : Matrix (Fin 2) (Fin 2) K) :
    pairSourceReversal (A + B) =
      pairSourceReversal A + pairSourceReversal B := by
  simp [pairSourceReversal, mul_add, add_mul]

@[simp]
theorem recordSourceReversal_smul (c : K)
    (A : Matrix (Fin 2) (Fin 2) K) :
    recordSourceReversal (c • A) =
      c • recordSourceReversal A := by
  simp [recordSourceReversal]

@[simp]
theorem pairSourceReversal_smul (c : K)
    (A : Matrix (Fin 2) (Fin 2) K) :
    pairSourceReversal (c • A) =
      c • pairSourceReversal A := by
  simp [pairSourceReversal]

@[simp]
theorem recordSourceReversal_one :
    recordSourceReversal (1 : Matrix (Fin 2) (Fin 2) K) = 1 := by
  simpa [recordSourceReversal] using
    (recordPolarityMatrix_mul_self (K := K))

@[simp]
theorem pairSourceReversal_one :
    pairSourceReversal (1 : Matrix (Fin 2) (Fin 2) K) = 1 := by
  simpa [pairSourceReversal] using (pairRecordMatrix_mul_self (K := K))

/-- An individual source reversal acts as complex conjugation on the generated scalar plane. -/
@[simp]
theorem recordSourceReversal_sourceComplexScalar (a b : K) :
    recordSourceReversal (sourceComplexScalar a b) =
      sourceComplexScalar a (-b) := by
  simp [sourceComplexScalar]

/-- Either individual source reversal acts as complex conjugation on the generated scalar plane. -/
@[simp]
theorem pairSourceReversal_sourceComplexScalar (a b : K) :
    pairSourceReversal (sourceComplexScalar a b) =
      sourceComplexScalar a (-b) := by
  simp [sourceComplexScalar]

/-- **Joint-versus-independent fixed-algebra law.** Simultaneous source-pair reversal fixes the
generated complex scalar plane, but invariance under both source reversals independently leaves
exactly scalar multiples of the identity. -/
theorem individualSourceReversals_fixed_iff_scalar
    [CharZero K]
    (A : Matrix (Fin 2) (Fin 2) K) :
    recordSourceReversal A = A ∧ pairSourceReversal A = A ↔
      ∃ a : K, A = a • (1 : Matrix (Fin 2) (Fin 2) K) := by
  constructor
  · rintro ⟨hrecord, hpair⟩
    have hparity : sourcePairParity A = A := by
      rw [← record_pair_sourceReversal_eq_sourcePairParity A, hpair,
        hrecord]
    obtain ⟨a, b, rfl⟩ :=
      (sourcePairParity_fixed_iff_complexScalar A).mp hparity
    have hscalar :
        sourceComplexScalar a (-b) = sourceComplexScalar a b := by
      simpa using hrecord
    have hp : (a, -b) = (a, b) :=
      sourceComplexScalar_pair_injective hscalar
    have hbneg : -b = b := congrArg Prod.snd hp
    have hb : b = 0 := (CharZero.neg_eq_self_iff).mp hbneg
    refine ⟨a, ?_⟩
    simp [hb, sourceComplexScalar]
  · rintro ⟨a, rfl⟩
    constructor <;> simp

end GaloisForLFunctions.HTGeometry
