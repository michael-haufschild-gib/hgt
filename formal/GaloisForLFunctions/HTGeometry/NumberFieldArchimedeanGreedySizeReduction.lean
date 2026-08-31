import GaloisForLFunctions.HTGeometry.NumberFieldArchimedeanJacobiActionReduction
import GaloisForLFunctions.HTGeometry.NumberFieldArchimedeanJacobiSchur

/-!
# Upper-unitriangular transport of number-field greedy flags

Mixed size reduction changes a Jacobi basis by an integral upper-unitriangular matrix.  To combine
it with recursive primitive minimization one must prove that every first Schur tail transforms by
the corresponding tail matrix and that the greedy flag survives.  This module proves the required
real/Hermitian block identity and assembles an unconditional mass-greedy, size-reduced Jacobi
decomposition.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix
open scoped Matrix

noncomputable section

variable {n : ℕ}

/-- Upper shear supported in the first row. -/
def matrixFirstUpperShear {R : Type*} [Zero R] [One R]
    (r : Fin n → R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  fun i j => Fin.cases (Fin.cases 1 r j)
    (fun a => Fin.cases 0 (fun b => if a = b then 1 else 0) j) i

@[simp] theorem matrixFirstUpperShear_zero_zero {R : Type*} [Zero R] [One R]
    (r : Fin n → R) : matrixFirstUpperShear r 0 0 = 1 := rfl

@[simp] theorem matrixFirstUpperShear_zero_succ {R : Type*} [Zero R] [One R]
    (r : Fin n → R) (j : Fin n) : matrixFirstUpperShear r 0 j.succ = r j := rfl

@[simp] theorem matrixFirstUpperShear_succ_zero {R : Type*} [Zero R] [One R]
    (r : Fin n → R) (i : Fin n) : matrixFirstUpperShear r i.succ 0 = 0 := rfl

@[simp] theorem matrixFirstUpperShear_succ_succ {R : Type*} [Zero R] [One R]
    (r : Fin n → R) (i j : Fin n) :
    matrixFirstUpperShear r i.succ j.succ = if i = j then 1 else 0 := rfl

/-- First Schur descent is invariant under a first-row upper shear. -/
theorem matrixFirstSchur_upperShear_congr {R : Type*} [Field R] [StarRing R]
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (r : Fin n → R)
    (hA : Matrix.conjTranspose A = A) (h00 : A 0 0 ≠ 0) :
    matrixFirstSchur
        (Matrix.transpose (matrixFirstUpperShear r) * A *
          Matrix.conjTranspose (Matrix.transpose (matrixFirstUpperShear r))) =
      matrixFirstSchur A := by
  have hsym (i j : Fin (n + 1)) : star (A j i) = A i j := by
    have h := congrArg (fun M => M i j) hA
    simpa [Matrix.conjTranspose_apply] using h
  ext i j
  simp [matrixFirstSchur, matrixFirstTail, matrixFirstCross, matrixFirstHead,
    Matrix.mul_apply, Fin.sum_univ_succ, matrixFirstUpperShear,
    Matrix.conjTranspose_apply, Matrix.transpose_apply, hsym]
  field_simp
  simp_rw [show ∀ x : Fin n, star (if x = j then (1 : R) else 0) =
      if x = j then 1 else 0 by
    intro x
    split_ifs <;> simp]
  simp
  ring

/-- An upper-unitriangular matrix splits into its head-fixed tail lift and first-row shear. -/
theorem matrixFirstTailLift_mul_upperShear {R : Type*} [CommRing R]
    (U : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (hupper : ∀ i j, j < i → U i j = 0) (hunit : ∀ i, U i i = 1) :
    matrixFirstTailLift (matrixFirstTail U) *
        matrixFirstUpperShear (fun j => U 0 j.succ) = U := by
  ext i j
  refine Fin.cases ?_ (fun a => ?_) i
  · refine Fin.cases ?_ (fun b => ?_) j
    · simp [Matrix.mul_apply, Fin.sum_univ_succ, hunit]
    · simp [Matrix.mul_apply, Fin.sum_univ_succ]
  · refine Fin.cases ?_ (fun b => ?_) j
    · simp [Matrix.mul_apply, Fin.sum_univ_succ, hupper]
    · simp [Matrix.mul_apply, Fin.sum_univ_succ, matrixFirstTail]

theorem transpose_matrixFirstTailLift {R : Type*} [Zero R] [One R]
    (T : Matrix (Fin n) (Fin n) R) :
    Matrix.transpose (matrixFirstTailLift T) =
      matrixFirstTailLift (Matrix.transpose T) := by
  ext i j
  refine Fin.cases ?_ (fun a => ?_) i
  · refine Fin.cases ?_ (fun b => ?_) j <;> simp [Matrix.transpose_apply]
  · refine Fin.cases ?_ (fun b => ?_) j <;> simp [Matrix.transpose_apply]

/-- First Schur descent intertwines upper-unitriangular congruence with tail congruence. -/
theorem matrixFirstSchur_upperUnitriangular_congr
    {R : Type*} [Field R] [StarRing R]
    (A U : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (hA : Matrix.conjTranspose A = A) (h00 : A 0 0 ≠ 0)
    (hupper : ∀ i j, j < i → U i j = 0) (hunit : ∀ i, U i i = 1) :
    matrixFirstSchur (Matrix.transpose U * A *
        Matrix.conjTranspose (Matrix.transpose U)) =
      Matrix.transpose (matrixFirstTail U) * matrixFirstSchur A *
        Matrix.conjTranspose (Matrix.transpose (matrixFirstTail U)) := by
  let T := matrixFirstTail U
  let L := matrixFirstTailLift T
  let H := matrixFirstUpperShear (fun j => U 0 j.succ)
  have hfactor : L * H = U := matrixFirstTailLift_mul_upperShear U hupper hunit
  have hrewrite : Matrix.transpose U * A * Matrix.conjTranspose (Matrix.transpose U) =
      Matrix.transpose H *
          (Matrix.transpose L * A * Matrix.conjTranspose (Matrix.transpose L)) *
        Matrix.conjTranspose (Matrix.transpose H) := by
    rw [← hfactor, Matrix.transpose_mul, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  rw [hrewrite]
  have hLself : Matrix.conjTranspose
        (Matrix.transpose L * A * Matrix.conjTranspose (Matrix.transpose L)) =
      Matrix.transpose L * A * Matrix.conjTranspose (Matrix.transpose L) := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hA]
    exact (Matrix.mul_assoc _ _ _).symm
  have hL00 : (Matrix.transpose L * A *
      Matrix.conjTranspose (Matrix.transpose L)) 0 0 ≠ 0 := by
    simpa [L, Matrix.mul_apply, Fin.sum_univ_succ] using h00
  rw [matrixFirstSchur_upperShear_congr
    (Matrix.transpose L * A * Matrix.conjTranspose (Matrix.transpose L))
    (fun j => U 0 j.succ) hLself hL00]
  have hlift := matrixFirstSchur_lift_congr A (Matrix.transpose T)
  simpa [L, T, transpose_matrixFirstTailLift] using hlift

open NumberField
open scoped Classical ComplexOrder NumberField

variable {K : Type*} [Field K] [NumberField K]

theorem numberFieldIntegerMatrix_upper_of_mixedUpper
    (N : Matrix (Fin (n + 1)) (Fin (n + 1)) (𝓞 K))
    (hN : IsMixedUnipotentUpper (numberFieldMixedOrderMatrix N)) :
    ∀ i j, j < i → N i j = 0 := by
  intro i j hji
  have h := hN.upper i j hji
  change mixedEmbedding K ((N i j : 𝓞 K) : K) = 0 at h
  have hcast : ((N i j : 𝓞 K) : K) = 0 :=
    mixedEmbedding_injective K (by simpa using h)
  exact Subtype.ext hcast

theorem numberFieldIntegerMatrix_unit_of_mixedUpper
    (N : Matrix (Fin (n + 1)) (Fin (n + 1)) (𝓞 K))
    (hN : IsMixedUnipotentUpper (numberFieldMixedOrderMatrix N)) :
    ∀ i, N i i = 1 := by
  intro i
  have h := hN.unit i
  change mixedEmbedding K ((N i i : 𝓞 K) : K) = 1 at h
  have hcast : ((N i i : 𝓞 K) : K) = 1 :=
    mixedEmbedding_injective K (by simpa using h)
  exact Subtype.ext hcast

theorem matrixFirstTail_det_eq_one_of_mixedUpper
    (N : Matrix (Fin (n + 1)) (Fin (n + 1)) (𝓞 K))
    (hN : IsMixedUnipotentUpper (numberFieldMixedOrderMatrix N)) :
    (matrixFirstTail N).det = 1 := by
  have hupper : ∀ i j, j < i → matrixFirstTail N i j = 0 := by
    intro i j hji
    exact numberFieldIntegerMatrix_upper_of_mixedUpper N hN i.succ j.succ (by simpa)
  have hunit : ∀ i, matrixFirstTail N i i = 1 := by
    intro i
    exact numberFieldIntegerMatrix_unit_of_mixedUpper N hN i.succ
  rw [Matrix.det_of_upperTriangular hupper]
  simp [hunit]

omit [NumberField K] in
theorem matrixFirstTail_numberFieldRealOrderMatrixAt
    (w : {w : InfinitePlace K // w.IsReal})
    (N : Matrix (Fin (n + 1)) (Fin (n + 1)) (𝓞 K)) :
    matrixFirstTail (numberFieldRealOrderMatrixAt w N) =
      numberFieldRealOrderMatrixAt w (matrixFirstTail N) := by
  rfl

omit [NumberField K] in
theorem matrixFirstTail_numberFieldComplexOrderMatrixAt
    (w : {w : InfinitePlace K // w.IsComplex})
    (N : Matrix (Fin (n + 1)) (Fin (n + 1)) (𝓞 K)) :
    matrixFirstTail (numberFieldComplexOrderMatrixAt w N) =
      numberFieldComplexOrderMatrixAt w (matrixFirstTail N) := by
  rfl

omit [NumberField K] in
theorem IsMixedUnipotentUpper.firstTail
    {V : Matrix (Fin (n + 1)) (Fin (n + 1)) (mixedEmbedding.mixedSpace K)}
    (hV : IsMixedUnipotentUpper V) :
    IsMixedUnipotentUpper (matrixFirstTail V) where
  upper i j hji := hV.upper i.succ j.succ (by simpa)
  unit i := hV.unit i.succ

omit [NumberField K] in
theorem numberFieldMixedOrderMatrix_firstTail
    (N : Matrix (Fin (n + 1)) (Fin (n + 1)) (𝓞 K)) :
    numberFieldMixedOrderMatrix (matrixFirstTail N) =
      matrixFirstTail (numberFieldMixedOrderMatrix N) := by
  rfl

theorem mulVec_firstCoordinate_of_mixedUpper
    (N : Matrix (Fin (n + 1)) (Fin (n + 1)) (𝓞 K))
    (hN : IsMixedUnipotentUpper (numberFieldMixedOrderMatrix N)) :
    N.mulVec (numberFieldCoordinateBasis (K := K) (0 : Fin (n + 1))) =
      numberFieldCoordinateBasis (K := K) (0 : Fin (n + 1)) := by
  rw [mulVec_numberFieldCoordinateBasis]
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [numberFieldCoordinateBasis,
      numberFieldIntegerMatrix_unit_of_mixedUpper N hN]
  · simp [numberFieldCoordinateBasis,
      numberFieldIntegerMatrix_upper_of_mixedUpper N hN]

/-- First Schur descent intertwines every mixed upper-unitriangular integral congruence with its
tail congruence. -/
theorem exists_numberFieldArchimedeanSchur_transposeConj_mixedUpper
    (A : numberFieldArchimedeanPositiveForms K (n + 1))
    (N : Matrix (Fin (n + 1)) (Fin (n + 1)) (𝓞 K))
    (hdet : N.det = 1)
    (hN : IsMixedUnipotentUpper (numberFieldMixedOrderMatrix N)) :
    ∃ htail : (matrixFirstTail N).det = 1,
      numberFieldArchimedeanSchur
          ((numberFieldTransposeSpecialLinear N hdet) • A) =
        (numberFieldTransposeSpecialLinear (matrixFirstTail N) htail) •
          numberFieldArchimedeanSchur A := by
  have htail : (matrixFirstTail N).det = 1 :=
    matrixFirstTail_det_eq_one_of_mixedUpper N hN
  refine ⟨htail, ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · funext w
    apply Subtype.ext
    let U := numberFieldRealOrderMatrixAt w N
    let M := (A.1.1 w : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    have hU := numberFieldRealOrderMatrixAt_unipotentUpper N hN w
    have hM : Matrix.conjTranspose M = M := (A.1.1 w).prop
    have hM00 : M 0 0 ≠ 0 := ne_of_gt (A.2.1 w).diag_pos
    have hs := matrixFirstSchur_upperUnitriangular_congr M U hM hM00 hU.1 hU.2
    change matrixFirstSchur
        (Matrix.transpose U * M * Matrix.conjTranspose (Matrix.transpose U)) =
      Matrix.transpose (matrixFirstTail U) * matrixFirstSchur M *
        Matrix.conjTranspose (Matrix.transpose (matrixFirstTail U))
    exact hs
  · funext w
    apply Subtype.ext
    let U := numberFieldComplexOrderMatrixAt w N
    let M := (A.1.2 w : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    have hUupper : ∀ i j, j < i → U i j = 0 :=
      numberFieldComplexOrderMatrixAt_upper N hN w
    have hUunit : ∀ i, U i i = 1 :=
      numberFieldComplexOrderMatrixAt_unit N hN w
    have hM : Matrix.conjTranspose M = M := (A.1.2 w).prop
    have hM00 : M 0 0 ≠ 0 := ne_of_gt (A.2.2 w).diag_pos
    have hs := matrixFirstSchur_upperUnitriangular_congr
      M U hM hM00 hUupper hUunit
    change matrixFirstSchur
        (Matrix.transpose U * M * Matrix.conjTranspose (Matrix.transpose U)) =
      Matrix.transpose (matrixFirstTail U) * matrixFirstSchur M *
        Matrix.conjTranspose (Matrix.transpose (matrixFirstTail U))
    exact hs

/-- Recursive primitive minimality is preserved by every upper-unitriangular integral change of
basis. -/
theorem NumberFieldArchimedeanGreedyFlag.transposeConj_mixedUpper :
    ∀ (m : ℕ) (A : numberFieldArchimedeanPositiveForms K m)
      (N : Matrix (Fin m) (Fin m) (𝓞 K)) (hdet : N.det = 1)
      (_hN : IsMixedUnipotentUpper (numberFieldMixedOrderMatrix N)),
      NumberFieldArchimedeanGreedyFlag m A →
        NumberFieldArchimedeanGreedyFlag m
          ((numberFieldTransposeSpecialLinear N hdet) • A) := by
  intro m
  induction m using Nat.twoStepInduction with
  | zero =>
      intro A N hdet hN hgreedy
      trivial
  | one =>
      intro A N hdet hN hgreedy
      trivial
  | more m ih0 ih1 =>
      intro A N hdet hN hgreedy
      change (_ ∧ _) at hgreedy
      change (_ ∧ _)
      constructor
      · intro b hb
        change numberFieldArchimedeanEnergy
              ((transposeSpecialLinearOfDetOne N hdet) • A)
              (numberFieldIntegerVectorEmbedding K
                (numberFieldCoordinateBasis (K := K) (0 : Fin (m + 2)))) ≤
            numberFieldArchimedeanEnergy
              ((transposeSpecialLinearOfDetOne N hdet) • A)
              (numberFieldIntegerVectorEmbedding K b)
        rw [numberFieldArchimedeanEnergy_transposeSpecialLinear,
          numberFieldArchimedeanEnergy_transposeSpecialLinear,
          mulVec_firstCoordinate_of_mixedUpper N hN]
        exact hgreedy.1 (N.mulVec b) (hb.detOne_mulVec N hdet)
      · obtain ⟨htail, hschur⟩ :=
          exists_numberFieldArchimedeanSchur_transposeConj_mixedUpper A N hdet hN
        rw [hschur]
        apply ih1 (numberFieldArchimedeanSchur A) (matrixFirstTail N) htail
        · rw [numberFieldMixedOrderMatrix_firstTail]
          exact hN.firstTail
        · exact hgreedy.2

/-- Every corrected archimedean form admits one mass-greedy simultaneous Jacobi decomposition
whose real and complex upper factors are uniformly size reduced. -/
theorem exists_numberFieldArchimedean_massGreedySizeReducedJacobiRadius
    (K : Type*) [Field K] [NumberField K] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (m : ℕ)
      (A : numberFieldArchimedeanPositiveForms K m),
      ∃ (B : Matrix (Fin m) (Fin m) (𝓞 K)) (hB : B.det = 1),
        let A₀ := numberFieldArchimedeanPositiveConj
          (transposeSpecialLinearOfDetOne B hB) A
        ∃ (N : Matrix (Fin m) (Fin m) (𝓞 K)) (hNdet : N.det = 1)
          (_hN : IsMixedUnipotentUpper (numberFieldMixedOrderMatrix N)),
          let A₁ := (numberFieldTransposeSpecialLinear N hNdet) • A₀
          ∃ J₁ : NumberFieldArchimedeanJacobiData A₁,
            J₁.IsMassGreedy m A₁ ∧
            (∀ w i j, i < j → |J₁.realU w i j| ≤ C) ∧
            ∀ w i j, i < j → ‖J₁.complexU w i j‖ ≤ C := by
  obtain ⟨C, hC, hreduce⟩ :=
    exists_numberFieldArchimedeanJacobi_sizeReductionRadius K
  refine ⟨C, hC, ?_⟩
  intro m A
  obtain ⟨B, hB, hflag⟩ := exists_numberFieldArchimedean_greedyFlag K m A
  let A₀ := numberFieldArchimedeanPositiveConj
    (transposeSpecialLinearOfDetOne B hB) A
  let J₀ : NumberFieldArchimedeanJacobiData A₀ :=
    Classical.choice (exists_numberFieldArchimedeanJacobiData A₀)
  obtain ⟨N, hNdet, hN, hreal, hcomplex⟩ := hreduce m A₀ J₀
  let A₁ := (numberFieldTransposeSpecialLinear N hNdet) • A₀
  let J₁ : NumberFieldArchimedeanJacobiData A₁ :=
    numberFieldArchimedeanJacobiTransposeConj A₀ J₀ N hNdet hN
  have hflag₁ : NumberFieldArchimedeanGreedyFlag m A₁ :=
    hflag.transposeConj_mixedUpper m A₀ N hNdet hN
  have hgreedy : J₁.IsMassGreedy m A₁ :=
    J₁.isMassGreedy_of_greedyFlag m A₁ hflag₁
  exact ⟨B, hB, N, hNdet, hN, J₁, hgreedy, hreal, hcomplex⟩

end

end GaloisForLFunctions.HTGeometry
