import GaloisForLFunctions.HTGeometry.FiniteBuresComparisonLaw

/-!
# Finite Bures data processing for rectangular Kraus channels

This module proves the matrix infrastructure behind Bures data processing.
A channel may change carrier dimension.  Its normalized rectangular Kraus
family supplies both Schrödinger evolution and the unital Heisenberg
pullback.  The key theorem is the inverse-pullback inequality; Alberti's
variational identity then gives fidelity monotonicity without purification.
-/

open Matrix
open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A normalized finite rectangular Kraus family.  `operator a` maps the
input carrier to the output carrier, and completeness is trace preservation. -/
structure FiniteRectangularKrausChannel
    (dIn dOut : ℕ) (κ : Type*) [Fintype κ] [DecidableEq κ] where
  operator : κ → Matrix (Fin dOut) (Fin dIn) ℂ
  completeness : ∑ a, (operator a)ᴴ * operator a = 1

/-- Schrödinger evolution of a finite rectangular Kraus channel. -/
def FiniteRectangularKrausChannel.evolveMatrix
    {dIn dOut : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]
    (Phi : FiniteRectangularKrausChannel dIn dOut κ)
    (C : Matrix (Fin dIn) (Fin dIn) ℂ) :
    Matrix (Fin dOut) (Fin dOut) ℂ :=
  ∑ a, Phi.operator a * C * (Phi.operator a)ᴴ

/-- Unital Heisenberg pullback of a finite rectangular Kraus channel. -/
def FiniteRectangularKrausChannel.pullbackMatrix
    {dIn dOut : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]
    (Phi : FiniteRectangularKrausChannel dIn dOut κ)
    (A : Matrix (Fin dOut) (Fin dOut) ℂ) :
    Matrix (Fin dIn) (Fin dIn) ℂ :=
  ∑ a, (Phi.operator a)ᴴ * A * Phi.operator a

theorem FiniteRectangularKrausChannel.evolveMatrix_posSemidef
    {dIn dOut : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]
    (Phi : FiniteRectangularKrausChannel dIn dOut κ)
    {C : Matrix (Fin dIn) (Fin dIn) ℂ} (hC : C.PosSemidef) :
    (Phi.evolveMatrix C).PosSemidef := by
  unfold FiniteRectangularKrausChannel.evolveMatrix
  apply Matrix.posSemidef_sum Finset.univ
  intro a _
  exact hC.mul_mul_conjTranspose_same (Phi.operator a)

theorem FiniteRectangularKrausChannel.pullbackMatrix_posSemidef
    {dIn dOut : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]
    (Phi : FiniteRectangularKrausChannel dIn dOut κ)
    {A : Matrix (Fin dOut) (Fin dOut) ℂ} (hA : A.PosSemidef) :
    (Phi.pullbackMatrix A).PosSemidef := by
  unfold FiniteRectangularKrausChannel.pullbackMatrix
  apply Matrix.posSemidef_sum Finset.univ
  intro a _
  exact hA.conjTranspose_mul_mul_same (Phi.operator a)

/-- Exact Schrödinger--Heisenberg trace duality. -/
theorem FiniteRectangularKrausChannel.trace_evolve_mul
    {dIn dOut : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]
    (Phi : FiniteRectangularKrausChannel dIn dOut κ)
    (C : Matrix (Fin dIn) (Fin dIn) ℂ)
    (A : Matrix (Fin dOut) (Fin dOut) ℂ) :
    (Phi.evolveMatrix C * A).trace = (C * Phi.pullbackMatrix A).trace := by
  unfold FiniteRectangularKrausChannel.evolveMatrix
    FiniteRectangularKrausChannel.pullbackMatrix
  rw [Finset.sum_mul, Matrix.mul_sum, Matrix.trace_sum, Matrix.trace_sum]
  apply Finset.sum_congr rfl
  intro a _
  calc
    (Phi.operator a * C * (Phi.operator a)ᴴ * A).trace =
        (((Phi.operator a)ᴴ * A) * (Phi.operator a * C)).trace := by
      rw [show Phi.operator a * C * (Phi.operator a)ᴴ * A =
        (Phi.operator a * C) * ((Phi.operator a)ᴴ * A) by
          simp only [Matrix.mul_assoc],
        Matrix.trace_mul_comm]
    _ = (C * ((Phi.operator a)ᴴ * A * Phi.operator a)).trace := by
      rw [show ((Phi.operator a)ᴴ * A) * (Phi.operator a * C) =
        ((Phi.operator a)ᴴ * A * Phi.operator a) * C by
          simp only [Matrix.mul_assoc],
        Matrix.trace_mul_comm]
    _ = (C * ((Phi.operator a)ᴴ * A * Phi.operator a)).trace := by
      rfl

/-- Completeness makes the Heisenberg pullback unital. -/
theorem FiniteRectangularKrausChannel.pullbackMatrix_one
    {dIn dOut : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]
    (Phi : FiniteRectangularKrausChannel dIn dOut κ) :
    Phi.pullbackMatrix 1 = 1 := by
  simpa [FiniteRectangularKrausChannel.pullbackMatrix] using Phi.completeness

/-- Stack the square-root-weighted Kraus operators into one rectangular
matrix.  Its Gram operator is the pullback of the reporter. -/
def FiniteRectangularKrausChannel.sqrtStack
    {dIn dOut : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]
    (Phi : FiniteRectangularKrausChannel dIn dOut κ)
    (A : Matrix (Fin dOut) (Fin dOut) ℂ) :
    Matrix (κ × Fin dOut) (Fin dIn) ℂ :=
  fun p i => (CFC.sqrt A * Phi.operator p.1) p.2 i

theorem FiniteRectangularKrausChannel.sqrtStack_conjTranspose_mul_self
    {dIn dOut : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]
    (Phi : FiniteRectangularKrausChannel dIn dOut κ)
    {A : Matrix (Fin dOut) (Fin dOut) ℂ} (hA : A.PosSemidef) :
    (Phi.sqrtStack A)ᴴ * Phi.sqrtStack A = Phi.pullbackMatrix A := by
  classical
  ext i j
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp only [FiniteRectangularKrausChannel.sqrtStack,
    Matrix.conjTranspose_apply,
    FiniteRectangularKrausChannel.pullbackMatrix, Matrix.sum_apply]
  have hS : (CFC.sqrt A)ᴴ = CFC.sqrt A := by
    simpa [Matrix.star_eq_conjTranspose] using (CFC.sqrt_nonneg A).star_eq
  have hS2 : CFC.sqrt A * CFC.sqrt A = A := by
    simpa [pow_two] using CFC.sq_sqrt A hA.nonneg
  apply Finset.sum_congr rfl
  intro a _
  have hmat : (CFC.sqrt A * Phi.operator a)ᴴ *
      (CFC.sqrt A * Phi.operator a) =
      (Phi.operator a)ᴴ * A * Phi.operator a := by
    rw [Matrix.conjTranspose_mul, hS]
    calc
      ((Phi.operator a)ᴴ * CFC.sqrt A) *
          (CFC.sqrt A * Phi.operator a) =
          (Phi.operator a)ᴴ *
            (CFC.sqrt A * (CFC.sqrt A * Phi.operator a)) :=
        Matrix.mul_assoc _ _ _
      _ = (Phi.operator a)ᴴ *
          ((CFC.sqrt A * CFC.sqrt A) * Phi.operator a) := by
        rw [← Matrix.mul_assoc (CFC.sqrt A) (CFC.sqrt A)]
      _ = (Phi.operator a)ᴴ * (A * Phi.operator a) := by rw [hS2]
      _ = ((Phi.operator a)ᴴ * A) * Phi.operator a :=
        (Matrix.mul_assoc _ _ _).symm
  exact congrArg (fun M : Matrix (Fin dIn) (Fin dIn) ℂ => M i j) hmat

theorem FiniteRectangularKrausChannel.sqrtStack_mulVec_injective
    {dIn dOut : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]
    (Phi : FiniteRectangularKrausChannel dIn dOut κ)
    {A : Matrix (Fin dOut) (Fin dOut) ℂ} (hA : A.PosDef) :
    Function.Injective (Phi.sqrtStack A).mulVec := by
  classical
  intro v w hvw
  have hSunit : IsUnit (CFC.sqrt A) :=
    (CFC.isUnit_sqrt_iff A hA.posSemidef.nonneg).2 hA.isUnit
  have hK : ∀ a, Phi.operator a *ᵥ v = Phi.operator a *ᵥ w := by
    intro a
    apply Matrix.mulVec_injective_of_isUnit hSunit
    ext o
    have hrow := congrFun hvw (a, o)
    change ((CFC.sqrt A * Phi.operator a) *ᵥ v) o =
      ((CFC.sqrt A * Phi.operator a) *ᵥ w) o at hrow
    simpa only [← Matrix.mulVec_mulVec] using hrow
  have hcompV := congrArg (fun B : Matrix (Fin dIn) (Fin dIn) ℂ => B *ᵥ v)
    Phi.completeness
  have hcompW := congrArg (fun B : Matrix (Fin dIn) (Fin dIn) ℂ => B *ᵥ w)
    Phi.completeness
  rw [Matrix.one_mulVec] at hcompV hcompW
  rw [Matrix.sum_mulVec] at hcompV hcompW
  simp_rw [← Matrix.mulVec_mulVec] at hcompV hcompW
  simp_rw [hK] at hcompV
  exact hcompV.symm.trans hcompW

/-- A positive-definite reporter remains positive definite after normalized
Kraus pullback, even when no individual Kraus operator is injective. -/
theorem FiniteRectangularKrausChannel.pullbackMatrix_posDef
    {dIn dOut : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]
    (Phi : FiniteRectangularKrausChannel dIn dOut κ)
    {A : Matrix (Fin dOut) (Fin dOut) ℂ} (hA : A.PosDef) :
    (Phi.pullbackMatrix A).PosDef := by
  rw [← Phi.sqrtStack_conjTranspose_mul_self hA.posSemidef]
  exact Matrix.PosDef.conjTranspose_mul_self _
    (Phi.sqrtStack_mulVec_injective hA)

/-- Stack a common left multiplier against every Kraus operator. -/
def FiniteRectangularKrausChannel.leftStack
    {dIn dOut : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]
    (Phi : FiniteRectangularKrausChannel dIn dOut κ)
    (B : Matrix (Fin dOut) (Fin dOut) ℂ) :
    Matrix (κ × Fin dOut) (Fin dIn) ℂ :=
  fun p i => (B * Phi.operator p.1) p.2 i

/-- Cross-Gram identity for two left-weighted Kraus stacks. -/
theorem FiniteRectangularKrausChannel.leftStack_conjTranspose_mul_leftStack
    {dIn dOut : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]
    (Phi : FiniteRectangularKrausChannel dIn dOut κ)
    (B D : Matrix (Fin dOut) (Fin dOut) ℂ) :
    (Phi.leftStack B)ᴴ * Phi.leftStack D =
      Phi.pullbackMatrix (Bᴴ * D) := by
  classical
  ext i j
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp only [FiniteRectangularKrausChannel.leftStack,
    Matrix.conjTranspose_apply,
    FiniteRectangularKrausChannel.pullbackMatrix, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro a _
  have hmat : (B * Phi.operator a)ᴴ * (D * Phi.operator a) =
      (Phi.operator a)ᴴ * (Bᴴ * D) * Phi.operator a := by
    rw [Matrix.conjTranspose_mul]
    calc
      ((Phi.operator a)ᴴ * Bᴴ) * (D * Phi.operator a) =
          (Phi.operator a)ᴴ * (Bᴴ * (D * Phi.operator a)) :=
        Matrix.mul_assoc _ _ _
      _ = (Phi.operator a)ᴴ * ((Bᴴ * D) * Phi.operator a) := by
        rw [← Matrix.mul_assoc Bᴴ D]
      _ = ((Phi.operator a)ᴴ * (Bᴴ * D)) * Phi.operator a :=
        (Matrix.mul_assoc _ _ _).symm
  exact congrArg (fun M : Matrix (Fin dIn) (Fin dIn) ℂ => M i j) hmat

/-- The square-root stack is the generic left stack at `sqrt A`. -/
theorem FiniteRectangularKrausChannel.sqrtStack_eq_leftStack
    {dIn dOut : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]
    (Phi : FiniteRectangularKrausChannel dIn dOut κ)
    (A : Matrix (Fin dOut) (Fin dOut) ℂ) :
    Phi.sqrtStack A = Phi.leftStack (CFC.sqrt A) := rfl

/-- **Unital inverse Jensen defect.**  For every normalized finite rectangular
Kraus channel and every positive-definite output reporter, pullback of the
inverse dominates inverse of the pullback.  The difference is exhibited as
the Gram operator of an explicit least-squares residual stack. -/
theorem FiniteRectangularKrausChannel.inverse_pullback_defect_posSemidef
    {dIn dOut : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]
    (Phi : FiniteRectangularKrausChannel dIn dOut κ)
    {A : Matrix (Fin dOut) (Fin dOut) ℂ} (hA : A.PosDef) :
    (Phi.pullbackMatrix A⁻¹ - (Phi.pullbackMatrix A)⁻¹).PosSemidef := by
  classical
  let S : Matrix (Fin dOut) (Fin dOut) ℂ := CFC.sqrt A
  let T : Matrix (Fin dOut) (Fin dOut) ℂ := CFC.sqrt A⁻¹
  let P : Matrix (Fin dIn) (Fin dIn) ℂ := Phi.pullbackMatrix A
  let X : Matrix (κ × Fin dOut) (Fin dIn) ℂ := Phi.leftStack T
  let Y : Matrix (κ × Fin dOut) (Fin dIn) ℂ :=
    Phi.leftStack S * P⁻¹
  let R : Matrix (κ × Fin dOut) (Fin dIn) ℂ := X - Y
  have hA0 : 0 ≤ A := Matrix.nonneg_iff_posSemidef.mpr hA.posSemidef
  have hAinv : A⁻¹.PosDef := hA.inv
  have hAinv0 : 0 ≤ A⁻¹ :=
    Matrix.nonneg_iff_posSemidef.mpr hAinv.posSemidef
  have hP : P.PosDef := Phi.pullbackMatrix_posDef hA
  have hPdet : IsUnit P.det := P.isUnit_iff_isUnit_det.mp hP.isUnit
  have hSH : Sᴴ = S := by
    simpa [S, Matrix.star_eq_conjTranspose] using (CFC.sqrt_nonneg A).star_eq
  have hTH : Tᴴ = T := by
    simpa [T, Matrix.star_eq_conjTranspose] using (CFC.sqrt_nonneg A⁻¹).star_eq
  have hPinvH : P⁻¹ᴴ = P⁻¹ := by
    rw [Matrix.conjTranspose_nonsing_inv]
    exact congrArg Inv.inv (by simpa using hP.isHermitian.eq)
  have hS2 : S * S = A := by
    simpa [S, pow_two] using CFC.sq_sqrt A hA0
  have hT2 : T * T = A⁻¹ := by
    simpa [T, pow_two] using CFC.sq_sqrt A⁻¹ hAinv0
  have hSinv : T = S⁻¹ := by
    dsimp [S, T]
    rw [Matrix.nonsing_inv_eq_ringInverse, CFC.sqrt_ringInverse,
      ← Matrix.nonsing_inv_eq_ringInverse]
  have hSunit : IsUnit S := by
    dsimp [S]
    exact (CFC.isUnit_sqrt_iff A hA0).2 hA.isUnit
  have hSdet : IsUnit S.det := S.isUnit_iff_isUnit_det.mp hSunit
  have hTS : T * S = 1 := by
    rw [hSinv, Matrix.nonsing_inv_mul S hSdet]
  have hST : S * T = 1 := by
    rw [hSinv, Matrix.mul_nonsing_inv S hSdet]
  have hXX : Xᴴ * X = Phi.pullbackMatrix A⁻¹ := by
    dsimp [X]
    rw [Phi.leftStack_conjTranspose_mul_leftStack, hTH, hT2]
  have hSS : (Phi.leftStack S)ᴴ * Phi.leftStack S = P := by
    dsimp [P]
    rw [Phi.leftStack_conjTranspose_mul_leftStack, hSH, hS2]
  have hXS : Xᴴ * Phi.leftStack S = 1 := by
    dsimp [X]
    rw [Phi.leftStack_conjTranspose_mul_leftStack, hTH, hTS,
      Phi.pullbackMatrix_one]
  have hSX : (Phi.leftStack S)ᴴ * X = 1 := by
    dsimp [X]
    rw [Phi.leftStack_conjTranspose_mul_leftStack, hSH, hST,
      Phi.pullbackMatrix_one]
  have hXY : Xᴴ * Y = P⁻¹ := by
    dsimp [Y]
    rw [← Matrix.mul_assoc, hXS, Matrix.one_mul]
  have hYX : Yᴴ * X = P⁻¹ := by
    dsimp [Y]
    rw [Matrix.conjTranspose_mul, hPinvH, Matrix.mul_assoc, hSX,
      Matrix.mul_one]
  have hYY : Yᴴ * Y = P⁻¹ := by
    dsimp [Y]
    rw [Matrix.conjTranspose_mul, hPinvH, Matrix.mul_assoc,
      ← Matrix.mul_assoc (Phi.leftStack S)ᴴ (Phi.leftStack S), hSS,
      Matrix.mul_nonsing_inv P hPdet, Matrix.mul_one]
  have hRR : Rᴴ * R =
      Phi.pullbackMatrix A⁻¹ - (Phi.pullbackMatrix A)⁻¹ := by
    dsimp [R]
    rw [Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.mul_sub, hXX, hXY, hYX, hYY]
    dsimp [P]
    abel
  rw [← hRR]
  exact Matrix.posSemidef_conjTranspose_mul_self R

/-- Testing the inverse-Jensen defect against any positive input matrix gives
the corresponding trace-order inequality. -/
theorem FiniteRectangularKrausChannel.re_trace_mul_inverse_pullback_le
    {dIn dOut : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]
    (Phi : FiniteRectangularKrausChannel dIn dOut κ)
    {M : Matrix (Fin dIn) (Fin dIn) ℂ} (hM : M.PosSemidef)
    {A : Matrix (Fin dOut) (Fin dOut) ℂ} (hA : A.PosDef) :
    ((M * (Phi.pullbackMatrix A)⁻¹).trace).re ≤
      ((M * Phi.pullbackMatrix A⁻¹).trace).re := by
  have hnonneg := finiteMatrix_re_trace_mul_nonneg_of_posSemidef hM
    (Phi.inverse_pullback_defect_posSemidef hA)
  rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re] at hnonneg
  linarith

/-- Pulling an output reporter back through a normalized Kraus channel can
only lower its Alberti half-sum objective.  The source term is exactly dual;
the target term is controlled by the explicit inverse-Jensen defect. -/
theorem FiniteRectangularKrausChannel.reporterHalfSum_pullback_le
    {dIn dOut : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]
    (Phi : FiniteRectangularKrausChannel dIn dOut κ)
    {C M : Matrix (Fin dIn) (Fin dIn) ℂ}
    (hM : M.PosSemidef)
    {A : Matrix (Fin dOut) (Fin dOut) ℂ} (hA : A.PosDef) :
    finiteBuresReporterHalfSum C M (Phi.pullbackMatrix A) ≤
      finiteBuresReporterHalfSum (Phi.evolveMatrix C) (Phi.evolveMatrix M) A := by
  have htarget := Phi.re_trace_mul_inverse_pullback_le hM hA
  have hsourceTrace := congrArg Complex.re (Phi.trace_evolve_mul C A)
  have htargetTrace := congrArg Complex.re (Phi.trace_evolve_mul M A⁻¹)
  unfold finiteBuresReporterHalfSum
  rw [← htargetTrace] at htarget
  rw [hsourceTrace]
  linarith

/-- **Finite rectangular Kraus data processing.**  Bures root fidelity is
monotone under every normalized finite Kraus channel, including channels
that change carrier dimension and singular input pairs. -/
theorem FiniteRectangularKrausChannel.finiteBuresRootFidelity_le_evolve
    {dIn dOut : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]
    (Phi : FiniteRectangularKrausChannel dIn dOut κ)
    {C M : Matrix (Fin dIn) (Fin dIn) ℂ}
    (hC : C.PosSemidef) (hM : M.PosSemidef) :
    finiteBuresRootFidelity C M ≤
      finiteBuresRootFidelity (Phi.evolveMatrix C) (Phi.evolveMatrix M) := by
  have hEC : (Phi.evolveMatrix C).PosSemidef := Phi.evolveMatrix_posSemidef hC
  have hEM : (Phi.evolveMatrix M).PosSemidef := Phi.evolveMatrix_posSemidef hM
  rw [← finiteBuresReporterHalfSumCapacity_eq_rootFidelity hEC hEM]
  unfold finiteBuresReporterHalfSumCapacity
  apply le_csInf
    (finiteBuresReporterHalfSumCapacity_values_nonempty
      (Phi.evolveMatrix C) (Phi.evolveMatrix M))
  rintro q ⟨A, hA, rfl⟩
  calc
    finiteBuresRootFidelity C M =
        finiteBuresReporterHalfSumCapacity C M :=
      (finiteBuresReporterHalfSumCapacity_eq_rootFidelity hC hM).symm
    _ ≤ finiteBuresReporterHalfSum C M (Phi.pullbackMatrix A) :=
      finiteBuresReporterHalfSumCapacity_le_halfSum hC hM
        (Phi.pullbackMatrix_posDef hA)
    _ ≤ finiteBuresReporterHalfSum
        (Phi.evolveMatrix C) (Phi.evolveMatrix M) A :=
      Phi.reporterHalfSum_pullback_le hM hA

/-- Schrödinger evolution is continuous on the finite matrix space. -/
theorem FiniteRectangularKrausChannel.continuous_evolveMatrix
    {dIn dOut : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]
    (Phi : FiniteRectangularKrausChannel dIn dOut κ) :
    Continuous Phi.evolveMatrix := by
  unfold FiniteRectangularKrausChannel.evolveMatrix
  fun_prop

/-- Compact-family Bures capacity cannot decrease under a normalized finite
Kraus channel.  The target family is evolved pointwise. -/
theorem FiniteRectangularKrausChannel.compactBuresDualCapacity_le_evolve_image
    {dIn dOut : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]
    (Phi : FiniteRectangularKrausChannel dIn dOut κ)
    {C : Matrix (Fin dIn) (Fin dIn) ℂ} (hC : C.PosSemidef)
    {K : Set (Matrix (Fin dIn) (Fin dIn) ℂ)}
    (hKne : K.Nonempty) (hKcompact : IsCompact K)
    (hKpsd : K ⊆ {M : Matrix (Fin dIn) (Fin dIn) ℂ | M.PosSemidef}) :
    compactBuresDualCapacity C K ≤
      compactBuresDualCapacity (Phi.evolveMatrix C) (Phi.evolveMatrix '' K) := by
  have hImageCompact : IsCompact (Phi.evolveMatrix '' K) :=
    hKcompact.image Phi.continuous_evolveMatrix
  have hImagePsd : Phi.evolveMatrix '' K ⊆
      {M : Matrix (Fin dOut) (Fin dOut) ℂ | M.PosSemidef} := by
    rintro N ⟨M, hM, rfl⟩
    exact Phi.evolveMatrix_posSemidef (hKpsd hM)
  unfold compactBuresDualCapacity
  apply csSup_le (compactBuresDualValueSet_nonempty C hKne)
  rintro q ⟨M, hM, rfl⟩
  calc
    finiteBuresRootFidelity C M ≤
        finiteBuresRootFidelity (Phi.evolveMatrix C) (Phi.evolveMatrix M) :=
      Phi.finiteBuresRootFidelity_le_evolve hC (hKpsd hM)
    _ ≤ sSup (compactBuresDualValueSet
        (Phi.evolveMatrix C) (Phi.evolveMatrix '' K)) := by
      apply le_csSup
        (compactBuresDualValueSet_bddAbove
          (Phi.evolveMatrix C) hImageCompact hImagePsd)
      exact ⟨Phi.evolveMatrix M, ⟨M, hM, rfl⟩, rfl⟩

/-- Squared compact-family data processing, the exact capacity form used by
the Bures incidence law. -/
theorem FiniteRectangularKrausChannel.compactBuresDualCapacity_sq_le_evolve_image
    {dIn dOut : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]
    (Phi : FiniteRectangularKrausChannel dIn dOut κ)
    {C : Matrix (Fin dIn) (Fin dIn) ℂ} (hC : C.PosSemidef)
    {K : Set (Matrix (Fin dIn) (Fin dIn) ℂ)}
    (hKne : K.Nonempty) (hKcompact : IsCompact K)
    (hKpsd : K ⊆ {M : Matrix (Fin dIn) (Fin dIn) ℂ | M.PosSemidef}) :
    compactBuresDualCapacity C K ^ 2 ≤
      compactBuresDualCapacity (Phi.evolveMatrix C) (Phi.evolveMatrix '' K) ^ 2 := by
  have hle := Phi.compactBuresDualCapacity_le_evolve_image
    hC hKne hKcompact hKpsd
  have hleft : 0 ≤ compactBuresDualCapacity C K := by
    obtain ⟨M, hM⟩ := hKne
    apply (finiteBuresRootFidelity_nonneg (hKpsd hM)).trans
    unfold compactBuresDualCapacity
    exact le_csSup
      (compactBuresDualValueSet_bddAbove C hKcompact hKpsd)
      ⟨M, hM, rfl⟩
  exact pow_le_pow_left₀ hleft hle 2

/-! ## Arbitrary finite POVMs -/

/-- A finite positive-operator-valued measurement.  Effects may have any
rank and need not be mutually orthogonal. -/
structure FiniteMatrixPOVM (d m : ℕ) where
  effect : Fin m → Matrix (Fin d) (Fin d) ℂ
  effect_posSemidef : ∀ j, (effect j).PosSemidef
  completeness : ∑ j, effect j = 1

/-- Kraus refinement of a POVM: outcome `j` is recorded in the output basis,
while `a` resolves the discarded post-measurement carrier. -/
def FiniteMatrixPOVM.measurementKraus
    {d m : ℕ} (E : FiniteMatrixPOVM d m) (x : Fin m × Fin d) :
    Matrix (Fin m) (Fin d) ℂ :=
  (Matrix.single x.1 x.2 (1 : ℂ) : Matrix (Fin m) (Fin d) ℂ) *
    CFC.sqrt (E.effect x.1)

theorem FiniteMatrixPOVM.sum_measurementKraus_conjTranspose_mul_self
    {d m : ℕ} (E : FiniteMatrixPOVM d m) :
    ∑ x : Fin m × Fin d,
      (E.measurementKraus x)ᴴ * E.measurementKraus x = 1 := by
  classical
  rw [Fintype.sum_prod_type]
  calc
    ∑ j : Fin m, ∑ a : Fin d,
        (E.measurementKraus (j, a))ᴴ * E.measurementKraus (j, a) =
        ∑ j : Fin m, E.effect j := by
      apply Finset.sum_congr rfl
      intro j _
      let S : Matrix (Fin d) (Fin d) ℂ := CFC.sqrt (E.effect j)
      have hSH : Sᴴ = S := by
        simpa [S, Matrix.star_eq_conjTranspose] using
          (CFC.sqrt_nonneg (E.effect j)).star_eq
      have hS2 : S * S = E.effect j := by
        simpa [S, pow_two] using CFC.sq_sqrt (E.effect j)
          (Matrix.nonneg_iff_posSemidef.mpr (E.effect_posSemidef j))
      have hsingle : ∑ a : Fin d,
          (Matrix.single j a (1 : ℂ) : Matrix (Fin m) (Fin d) ℂ)ᴴ *
            (Matrix.single j a (1 : ℂ) : Matrix (Fin m) (Fin d) ℂ) = 1 := by
        calc
          ∑ a : Fin d,
              (Matrix.single j a (1 : ℂ) : Matrix (Fin m) (Fin d) ℂ)ᴴ *
                (Matrix.single j a (1 : ℂ) : Matrix (Fin m) (Fin d) ℂ) =
              ∑ a : Fin d, Matrix.single a a (1 : ℂ) := by
            apply Finset.sum_congr rfl
            intro a _
            rw [Matrix.conjTranspose_single, star_one,
              Matrix.single_mul_single_same, one_mul]
          _ = 1 := Matrix.sum_single_one
      calc
        ∑ a : Fin d,
            (E.measurementKraus (j, a))ᴴ * E.measurementKraus (j, a) =
            ∑ a : Fin d, Sᴴ *
              ((Matrix.single j a (1 : ℂ) : Matrix (Fin m) (Fin d) ℂ)ᴴ *
                (Matrix.single j a (1 : ℂ) : Matrix (Fin m) (Fin d) ℂ)) * S := by
          apply Finset.sum_congr rfl
          intro a _
          simp only [FiniteMatrixPOVM.measurementKraus,
            Matrix.conjTranspose_mul]
          dsimp [S]
          simp only [Matrix.mul_assoc]
        _ = Sᴴ * (∑ a : Fin d,
              (Matrix.single j a (1 : ℂ) : Matrix (Fin m) (Fin d) ℂ)ᴴ *
                (Matrix.single j a (1 : ℂ) : Matrix (Fin m) (Fin d) ℂ)) * S := by
          rw [Finset.mul_sum, Finset.sum_mul]
        _ = Sᴴ * 1 * S := by rw [hsingle]
        _ = E.effect j := by rw [Matrix.mul_one, hSH, hS2]
    _ = 1 := E.completeness

/-- Every POVM has a normalized rectangular Kraus realization. -/
def FiniteMatrixPOVM.measurementChannel
    {d m : ℕ} (E : FiniteMatrixPOVM d m) :
    FiniteRectangularKrausChannel d m (Fin m × Fin d) where
  operator := E.measurementKraus
  completeness := E.sum_measurementKraus_conjTranspose_mul_self

/-- A POVM refinement records one diagonal outcome block. -/
theorem FiniteMatrixPOVM.sum_measurementKraus_evolve_fixed
    {d m : ℕ} (E : FiniteMatrixPOVM d m)
    (C : Matrix (Fin d) (Fin d) ℂ) (j : Fin m) :
    ∑ a : Fin d, E.measurementKraus (j, a) * C *
        (E.measurementKraus (j, a))ᴴ =
      ((C * E.effect j).trace) • Matrix.single j j (1 : ℂ) := by
  classical
  let S : Matrix (Fin d) (Fin d) ℂ := CFC.sqrt (E.effect j)
  have hSH : Sᴴ = S := by
    simpa [S, Matrix.star_eq_conjTranspose] using
      (CFC.sqrt_nonneg (E.effect j)).star_eq
  have hS2 : S * S = E.effect j := by
    simpa [S, pow_two] using CFC.sq_sqrt (E.effect j)
      (Matrix.nonneg_iff_posSemidef.mpr (E.effect_posSemidef j))
  have hterm : ∀ a : Fin d,
      E.measurementKraus (j, a) * C * (E.measurementKraus (j, a))ᴴ =
        ((S * C * S) a a) • Matrix.single j j (1 : ℂ) := by
    intro a
    simp only [FiniteMatrixPOVM.measurementKraus,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_single, star_one]
    rw [hSH]
    rw [show
      ((Matrix.single j a (1 : ℂ) : Matrix (Fin m) (Fin d) ℂ) * S) * C *
          (S * Matrix.single a j (1 : ℂ)) =
        (Matrix.single j a (1 : ℂ) : Matrix (Fin m) (Fin d) ℂ) *
          (S * C * S) * Matrix.single a j (1 : ℂ) by
            simp only [Matrix.mul_assoc]]
    simp [Matrix.smul_single]
  simp_rw [hterm]
  rw [← Finset.sum_smul]
  have htrace : (S * C * S).trace = (C * E.effect j).trace := by
    rw [Matrix.trace_mul_cycle, hS2, Matrix.trace_mul_comm]
  change (S * C * S).trace • Matrix.single j j (1 : ℂ) =
    (C * E.effect j).trace • Matrix.single j j (1 : ℂ)
  rw [htrace]

/-- The Schrödinger output of the POVM channel is the diagonal matrix of its
Born trace pairings. -/
theorem FiniteMatrixPOVM.measurementChannel_evolveMatrix_eq_diagonal
    {d m : ℕ} (E : FiniteMatrixPOVM d m)
    (C : Matrix (Fin d) (Fin d) ℂ) :
    E.measurementChannel.evolveMatrix C =
      Matrix.diagonal (fun j => (C * E.effect j).trace) := by
  classical
  unfold FiniteRectangularKrausChannel.evolveMatrix
    FiniteMatrixPOVM.measurementChannel
  rw [Fintype.sum_prod_type]
  calc
    ∑ j : Fin m, ∑ a : Fin d,
        E.measurementKraus (j, a) * C * (E.measurementKraus (j, a))ᴴ =
        ∑ j : Fin m,
          ((C * E.effect j).trace) • Matrix.single j j (1 : ℂ) := by
      apply Finset.sum_congr rfl
      intro j _
      exact E.sum_measurementKraus_evolve_fixed C j
    _ = Matrix.diagonal (fun j => (C * E.effect j).trace) := by
      simpa [Matrix.smul_single] using
        (Matrix.sum_single_eq_diagonal
          (fun j : Fin m => (C * E.effect j).trace))

/-- Entrywise square root is the CFC square root of a nonnegative real
diagonal matrix. -/
theorem cfc_sqrt_diagonal_ofReal
    {m : ℕ} (p : Fin m → ℝ) (hp : ∀ j, 0 ≤ p j) :
    CFC.sqrt (Matrix.diagonal (fun j => (p j : ℂ))) =
      Matrix.diagonal (fun j => (Real.sqrt (p j) : ℂ)) := by
  apply CFC.sqrt_unique
  · rw [Matrix.diagonal_mul_diagonal]
    ext j k
    by_cases hjk : j = k
    · subst k
      simp only [Matrix.diagonal_apply_eq]
      rw [← pow_two]
      exact_mod_cast Real.sq_sqrt (hp j)
    · simp [hjk]
  · apply Matrix.nonneg_iff_posSemidef.mpr
    apply Matrix.PosSemidef.diagonal
    intro j
    change (0 : ℂ) ≤ (Real.sqrt (p j) : ℂ)
    exact Complex.nonneg_iff.mpr ⟨Real.sqrt_nonneg (p j), by simp⟩

/-- Classical Hellinger/Bhattacharyya affinity of two finite nonnegative
weight vectors. -/
def finiteHellingerAffinity {m : ℕ} (p q : Fin m → ℝ) : ℝ :=
  ∑ j, Real.sqrt (p j * q j)

/-- Bures root fidelity of real nonnegative diagonal matrices is exactly
their classical Hellinger affinity. -/
theorem finiteBuresRootFidelity_diagonal_ofReal
    {m : ℕ} (p q : Fin m → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hq : ∀ j, 0 ≤ q j) :
    finiteBuresRootFidelity
        (Matrix.diagonal (fun j => (p j : ℂ)))
        (Matrix.diagonal (fun j => (q j : ℂ))) =
      finiteHellingerAffinity p q := by
  let P : Matrix (Fin m) (Fin m) ℂ :=
    Matrix.diagonal (fun j => (p j : ℂ))
  let Q : Matrix (Fin m) (Fin m) ℂ :=
    Matrix.diagonal (fun j => (q j : ℂ))
  have hsqrtP : CFC.sqrt P =
      Matrix.diagonal (fun j => (Real.sqrt (p j) : ℂ)) := by
    exact cfc_sqrt_diagonal_ofReal p hp
  have hconj : CFC.conjSqrt P Q =
      Matrix.diagonal (fun j => ((p j * q j : ℝ) : ℂ)) := by
    rw [CFC.conjSqrt_apply, hsqrtP]
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    ext j k
    by_cases hjk : j = k
    · subst k
      simp only [Matrix.diagonal_apply_eq, Complex.ofReal_mul]
      have hsqp : (Real.sqrt (p j) : ℂ) ^ 2 = (p j : ℂ) := by
        exact_mod_cast Real.sq_sqrt (hp j)
      calc
        (Real.sqrt (p j) : ℂ) * (q j : ℂ) * (Real.sqrt (p j) : ℂ) =
            (Real.sqrt (p j) : ℂ) ^ 2 * (q j : ℂ) := by ring
        _ = (p j : ℂ) * (q j : ℂ) := by rw [hsqp]
    · simp [hjk]
  have hpq : ∀ j, 0 ≤ p j * q j := fun j => mul_nonneg (hp j) (hq j)
  unfold finiteBuresRootFidelity
  change (CFC.sqrt (CFC.conjSqrt P Q)).trace.re = _
  rw [hconj, cfc_sqrt_diagonal_ofReal (fun j => p j * q j) hpq]
  simp [finiteHellingerAffinity]

/-- The trace pairing of two positive semidefinite complex matrices is the
complex embedding of its real part. -/
theorem finiteMatrix_trace_mul_eq_ofReal_re_of_posSemidef
    {d : ℕ} {A B : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (A * B).trace = (((A * B).trace.re : ℝ) : ℂ) := by
  have hstar : star ((A * B).trace) = (A * B).trace := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul,
      hA.isHermitian.eq, hB.isHermitian.eq, Matrix.trace_mul_comm]
  exact (Complex.conj_eq_iff_re.mp hstar).symm

/-- A POVM channel output is the real diagonal of its nonnegative Born trace
pairings. -/
theorem FiniteMatrixPOVM.measurementChannel_evolveMatrix_eq_diagonal_ofReal
    {d m : ℕ} (E : FiniteMatrixPOVM d m)
    {C : Matrix (Fin d) (Fin d) ℂ} (hC : C.PosSemidef) :
    E.measurementChannel.evolveMatrix C =
      Matrix.diagonal (fun j => (((C * E.effect j).trace.re : ℝ) : ℂ)) := by
  rw [E.measurementChannel_evolveMatrix_eq_diagonal]
  congr 1
  funext j
  exact finiteMatrix_trace_mul_eq_ofReal_re_of_posSemidef
    hC (E.effect_posSemidef j)

/-- **POVM/Hellinger data processing.**  For every finite POVM, quantum
Bures root fidelity is bounded above by the classical Hellinger affinity of
the complete outcome distributions.  No projectivity, commutativity, or
full-rank assumption is imposed. -/
theorem FiniteMatrixPOVM.finiteBuresRootFidelity_le_finiteHellingerAffinity
    {d m : ℕ} (E : FiniteMatrixPOVM d m)
    {C M : Matrix (Fin d) (Fin d) ℂ}
    (hC : C.PosSemidef) (hM : M.PosSemidef) :
    finiteBuresRootFidelity C M ≤
      finiteHellingerAffinity
        (fun j => ((C * E.effect j).trace).re)
        (fun j => ((M * E.effect j).trace).re) := by
  have hp : ∀ j, 0 ≤ ((C * E.effect j).trace).re := fun j =>
    finiteMatrix_re_trace_mul_nonneg_of_posSemidef hC
      (E.effect_posSemidef j)
  have hq : ∀ j, 0 ≤ ((M * E.effect j).trace).re := fun j =>
    finiteMatrix_re_trace_mul_nonneg_of_posSemidef hM
      (E.effect_posSemidef j)
  have hdata := E.measurementChannel.finiteBuresRootFidelity_le_evolve hC hM
  rw [E.measurementChannel_evolveMatrix_eq_diagonal_ofReal hC,
    E.measurementChannel_evolveMatrix_eq_diagonal_ofReal hM,
    finiteBuresRootFidelity_diagonal_ofReal _ _ hp hq] at hdata
  exact hdata

end

end GaloisForLFunctions.HTGeometry
