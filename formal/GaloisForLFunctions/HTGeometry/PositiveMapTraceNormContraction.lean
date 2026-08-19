import GaloisForLFunctions.HTGeometry.AncillaBlockMatrix
import GaloisForLFunctions.HTGeometry.PositiveTraceContraction

/-!
# Trace-norm contraction for two-positive trace-preserving maps

A positive trace-preserving map contracts the nuclear norm of a Hermitian matrix
(`finiteMatrixNuclearNorm_apply_le`).  For a general -- not necessarily Hermitian -- matrix the
same bound holds as soon as the map is two-positive, by the Hermitian dilation

`X ↦ [[0, X], [Xᴴ, 0]]`,

whose nuclear norm is exactly twice that of `X` and which is intertwined with `X` by any
star-preserving map.  Positivity already forces star preservation, so no extra hypothesis is
needed beyond linearity, two-positivity and trace preservation.
-/

open Matrix
open scoped Matrix ComplexOrder MatrixOrder BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## Block diagonal matrices with a two-dimensional ancilla -/

/-- The block diagonal matrix with entries `P` and `Q`. -/
def blockDiag2 (P Q : Matrix n n ℂ) : Matrix (n × Fin 2) (n × Fin 2) ℂ :=
  blockMat ![![P, 0], ![0, Q]]

theorem blockDiag2_mul (P Q R S : Matrix n n ℂ) :
    blockDiag2 P Q * blockDiag2 R S = blockDiag2 (P * R) (Q * S) := by
  rw [blockDiag2, blockDiag2, blockDiag2, blockMat_mul]
  congr 1
  funext a b
  fin_cases a <;> fin_cases b <;> simp [Fin.sum_univ_two]

omit [Fintype n] [DecidableEq n] in
theorem blockDiag2_conjTranspose (P Q : Matrix n n ℂ) :
    (blockDiag2 P Q)ᴴ = blockDiag2 Pᴴ Qᴴ := by
  rw [blockDiag2, blockDiag2, blockMat_conjTranspose]
  congr 1
  funext a b
  fin_cases a <;> fin_cases b <;> simp

omit [DecidableEq n] in
theorem blockDiag2_trace (P Q : Matrix n n ℂ) :
    (blockDiag2 P Q).trace = P.trace + Q.trace := by
  rw [blockDiag2, blockMat_trace, Fin.sum_univ_two]
  simp

/-- The block diagonal of two positive semidefinite matrices is positive semidefinite. -/
theorem blockDiag2_posSemidef {P Q : Matrix n n ℂ} (hP : P.PosSemidef) (hQ : Q.PosSemidef) :
    (blockDiag2 P Q).PosSemidef := by
  have hPs : (CFC.sqrt P)ᴴ = CFC.sqrt P := by
    simpa [Matrix.star_eq_conjTranspose] using (CFC.sqrt_nonneg P).star_eq
  have hQs : (CFC.sqrt Q)ᴴ = CFC.sqrt Q := by
    simpa [Matrix.star_eq_conjTranspose] using (CFC.sqrt_nonneg Q).star_eq
  have hPsq : CFC.sqrt P * CFC.sqrt P = P := by
    have := CFC.sq_sqrt P hP.nonneg
    rwa [pow_two] at this
  have hQsq : CFC.sqrt Q * CFC.sqrt Q = Q := by
    have := CFC.sq_sqrt Q hQ.nonneg
    rwa [pow_two] at this
  have hfac : blockDiag2 P Q
      = (blockDiag2 (CFC.sqrt P) (CFC.sqrt Q))ᴴ * blockDiag2 (CFC.sqrt P) (CFC.sqrt Q) := by
    rw [blockDiag2_conjTranspose, hPs, hQs, blockDiag2_mul, hPsq, hQsq]
  rw [hfac]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- The positive square root of a block diagonal is the block diagonal of the square roots. -/
theorem sqrt_blockDiag2 {P Q : Matrix n n ℂ} (hP : P.PosSemidef) (hQ : Q.PosSemidef) :
    CFC.sqrt (blockDiag2 P Q) = blockDiag2 (CFC.sqrt P) (CFC.sqrt Q) := by
  have hPsq : CFC.sqrt P * CFC.sqrt P = P := by
    have := CFC.sq_sqrt P hP.nonneg
    rwa [pow_two] at this
  have hQsq : CFC.sqrt Q * CFC.sqrt Q = Q := by
    have := CFC.sq_sqrt Q hQ.nonneg
    rwa [pow_two] at this
  refine CFC.sqrt_unique ?_ ?_
  · rw [blockDiag2_mul, hPsq, hQsq]
  · have := blockDiag2_posSemidef (CFC.sqrt_nonneg P |> fun h => by
      simpa using Matrix.le_iff.mp h) (CFC.sqrt_nonneg Q |> fun h => by
      simpa using Matrix.le_iff.mp h)
    simpa using Matrix.le_iff.mpr (by simpa using this)

/-! ## The Hermitian dilation -/

/-- The Hermitian dilation `[[0, X], [Xᴴ, 0]]` of an arbitrary square matrix. -/
def hermDilation2 (X : Matrix n n ℂ) : Matrix (n × Fin 2) (n × Fin 2) ℂ :=
  blockMat ![![0, X], ![Xᴴ, 0]]

omit [Fintype n] [DecidableEq n] in
theorem hermDilation2_isHermitian (X : Matrix n n ℂ) : (hermDilation2 X).IsHermitian := by
  show (hermDilation2 X)ᴴ = hermDilation2 X
  rw [hermDilation2, blockMat_conjTranspose]
  congr 1
  funext a b
  fin_cases a <;> fin_cases b <;> simp

theorem hermDilation2_mul_self (X : Matrix n n ℂ) :
    hermDilation2 X * hermDilation2 X = blockDiag2 (X * Xᴴ) (Xᴴ * X) := by
  rw [hermDilation2, blockMat_mul, blockDiag2]
  congr 1
  funext a b
  fin_cases a <;> fin_cases b <;> simp [Fin.sum_univ_two]

/-- **The dilation doubles the nuclear norm.** -/
theorem finiteMatrixNuclearNorm_hermDilation2 (X : Matrix n n ℂ) :
    finiteMatrixNuclearNorm (hermDilation2 X) = 2 * finiteMatrixNuclearNorm X := by
  have hgram : (hermDilation2 X)ᴴ * hermDilation2 X = blockDiag2 (X * Xᴴ) (Xᴴ * X) := by
    rw [hermDilation2_isHermitian X, hermDilation2_mul_self]
  have hP : (X * Xᴴ).PosSemidef := Matrix.posSemidef_self_mul_conjTranspose X
  have hQ : (Xᴴ * X).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self X
  rw [finiteMatrixNuclearNorm_eq_trace_sqrt_re, hgram, sqrt_blockDiag2 hP hQ, blockDiag2_trace]
  have hXH : finiteMatrixNuclearNorm Xᴴ = (CFC.sqrt (X * Xᴴ)).trace.re := by
    rw [finiteMatrixNuclearNorm_eq_trace_sqrt_re]
    simp
  have hX : finiteMatrixNuclearNorm X = (CFC.sqrt (Xᴴ * X)).trace.re :=
    finiteMatrixNuclearNorm_eq_trace_sqrt_re X
  rw [Complex.add_re, ← hXH, ← hX, finiteMatrixNuclearNorm_conjTranspose]
  ring

/-! ## Positive trace-preserving maps -/

/-- A linear, positive, trace-preserving map of matrices. -/
structure IsPositiveTP (Φ : Matrix n n ℂ → Matrix n n ℂ) : Prop where
  map_add : ∀ X Y, Φ (X + Y) = Φ X + Φ Y
  map_smul : ∀ (c : ℂ) (X), Φ (c • X) = c • Φ X
  pos : ∀ X : Matrix n n ℂ, X.PosSemidef → (Φ X).PosSemidef
  tp : ∀ X : Matrix n n ℂ, (Φ X).trace = X.trace

/-! ### Positive linear maps

Everything below the `tp` field uses only linearity and positivity, so it is stated for those
three hypotheses directly and then re-exposed on `IsPositiveTP`. -/

section PositiveLinear

variable {Φ : Matrix n n ℂ → Matrix n n ℂ}

omit [Fintype n] [DecidableEq n] in
theorem positiveLinear_map_zero (hsmul : ∀ (c : ℂ) (X), Φ (c • X) = c • Φ X) : Φ 0 = 0 := by
  have := hsmul 0 0
  simpa using this

omit [Fintype n] [DecidableEq n] in
theorem positiveLinear_map_neg (hsmul : ∀ (c : ℂ) (X), Φ (c • X) = c • Φ X)
    (X : Matrix n n ℂ) : Φ (-X) = -Φ X := by
  have := hsmul (-1) X
  simpa using this

omit [Fintype n] [DecidableEq n] in
theorem positiveLinear_map_sub (hadd : ∀ X Y, Φ (X + Y) = Φ X + Φ Y)
    (hsmul : ∀ (c : ℂ) (X), Φ (c • X) = c • Φ X) (X Y : Matrix n n ℂ) :
    Φ (X - Y) = Φ X - Φ Y := by
  rw [sub_eq_add_neg, hadd, positiveLinear_map_neg hsmul, ← sub_eq_add_neg]

/-- A positive map sends Hermitian matrices to Hermitian matrices. -/
theorem positiveLinear_map_isHermitian (hadd : ∀ X Y, Φ (X + Y) = Φ X + Φ Y)
    (hsmul : ∀ (c : ℂ) (X), Φ (c • X) = c • Φ X)
    (hpos : ∀ X : Matrix n n ℂ, X.PosSemidef → (Φ X).PosSemidef)
    {A : Matrix n n ℂ} (hA : A.IsHermitian) : (Φ A).IsHermitian := by
  have hsplit : Φ A = Φ (hermPos A) - Φ (hermNeg A) := by
    rw [← positiveLinear_map_sub hadd hsmul, hermPos_sub_hermNeg hA]
  rw [hsplit]
  exact ((hpos _ (hermPos_posSemidef A)).isHermitian).sub
    ((hpos _ (hermNeg_posSemidef A)).isHermitian)

/-- **A positive linear map is star preserving.** -/
theorem positiveLinear_map_conjTranspose (hadd : ∀ X Y, Φ (X + Y) = Φ X + Φ Y)
    (hsmul : ∀ (c : ℂ) (X), Φ (c • X) = c • Φ X)
    (hpos : ∀ X : Matrix n n ℂ, X.PosSemidef → (Φ X).PosSemidef) (X : Matrix n n ℂ) :
    Φ Xᴴ = (Φ X)ᴴ := by
  obtain ⟨A, hA⟩ : ∃ A : Matrix n n ℂ, A = (2⁻¹ : ℂ) • (X + Xᴴ) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : Matrix n n ℂ, B = ((2⁻¹ : ℂ) * (-Complex.I)) • (X - Xᴴ) := ⟨_, rfl⟩
  have h1 : A.IsHermitian := by
    show Aᴴ = A
    rw [hA, Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
      Matrix.conjTranspose_conjTranspose, add_comm]
    norm_num
  have hstarc : star ((2⁻¹ : ℂ) * (-Complex.I)) = -((2⁻¹ : ℂ) * (-Complex.I)) := by
    simp
  have h2 : B.IsHermitian := by
    show Bᴴ = B
    rw [hB, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_conjTranspose, hstarc, show Xᴴ - X = -(X - Xᴴ) by abel,
      smul_neg, neg_smul, neg_neg]
  have hI : Complex.I * ((2⁻¹ : ℂ) * (-Complex.I)) = (2⁻¹ : ℂ) := by
    have hII : Complex.I * -Complex.I = 1 := by rw [mul_neg, Complex.I_mul_I]; ring
    calc Complex.I * ((2⁻¹ : ℂ) * (-Complex.I))
        = (2⁻¹ : ℂ) * (Complex.I * -Complex.I) := by ring
      _ = (2⁻¹ : ℂ) := by rw [hII, mul_one]
  have hdecomp : X = A + Complex.I • B := by
    rw [hA, hB, smul_smul, hI, ← smul_add, show X + Xᴴ + (X - Xᴴ) = (2 : ℂ) • X by
      rw [two_smul]; abel, smul_smul]
    norm_num
  have hdecompH : Xᴴ = A - Complex.I • B := by
    conv_lhs => rw [hdecomp]
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, h1, h2]
    simp only [RCLike.star_def, Complex.conj_I, neg_smul, ← sub_eq_add_neg]
  rw [hdecompH, hdecomp, positiveLinear_map_sub hadd hsmul, hadd, hsmul,
    Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
    (positiveLinear_map_isHermitian hadd hsmul hpos h1).eq,
    (positiveLinear_map_isHermitian hadd hsmul hpos h2).eq]
  simp only [RCLike.star_def, Complex.conj_I, neg_smul, ← sub_eq_add_neg]

end PositiveLinear

namespace IsPositiveTP

variable {Φ : Matrix n n ℂ → Matrix n n ℂ}

omit [DecidableEq n] in
theorem map_zero (hΦ : IsPositiveTP Φ) : Φ 0 = 0 := positiveLinear_map_zero hΦ.map_smul

omit [DecidableEq n] in
theorem map_neg (hΦ : IsPositiveTP Φ) (X : Matrix n n ℂ) : Φ (-X) = -Φ X :=
  positiveLinear_map_neg hΦ.map_smul X

omit [DecidableEq n] in
theorem map_sub (hΦ : IsPositiveTP Φ) (X Y : Matrix n n ℂ) : Φ (X - Y) = Φ X - Φ Y :=
  positiveLinear_map_sub hΦ.map_add hΦ.map_smul X Y

/-- A positive map sends Hermitian matrices to Hermitian matrices. -/
theorem map_isHermitian (hΦ : IsPositiveTP Φ) {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    (Φ A).IsHermitian :=
  positiveLinear_map_isHermitian hΦ.map_add hΦ.map_smul hΦ.pos hA

/-- **A positive linear map is star preserving.** -/
theorem map_conjTranspose (hΦ : IsPositiveTP Φ) (X : Matrix n n ℂ) : Φ Xᴴ = (Φ X)ᴴ :=
  positiveLinear_map_conjTranspose hΦ.map_add hΦ.map_smul hΦ.pos X

/-- **Contraction of the nuclear norm on Hermitian matrices.** -/
theorem nuclearNorm_apply_le_of_isHermitian (hΦ : IsPositiveTP Φ) {A : Matrix n n ℂ}
    (hA : A.IsHermitian) : finiteMatrixNuclearNorm (Φ A) ≤ finiteMatrixNuclearNorm A :=
  finiteMatrixNuclearNorm_apply_le hΦ.map_sub hΦ.pos hΦ.tp hA

end IsPositiveTP

/-! ## The ancilla amplification of a positive trace-preserving map -/

/-- The two-fold amplification of a linear, two-positive, trace-preserving map is itself a
positive trace-preserving map. -/
theorem isPositiveTP_amplify {Φ : Matrix n n ℂ → Matrix n n ℂ} (hΦ : IsPositiveTP Φ)
    {m : Type*} [Fintype m] [DecidableEq m]
    (hpos : ∀ X : Matrix (n × m) (n × m) ℂ, X.PosSemidef → (amplify Φ m X).PosSemidef) :
    IsPositiveTP (amplify Φ m) where
  map_add := by
    intro X Y
    ext p q
    rw [Matrix.add_apply, amplify_apply, amplify_apply, amplify_apply,
      show (fun i j => (X + Y) (i, p.2) (j, q.2))
        = matBlock X p.2 q.2 + matBlock Y p.2 q.2 from rfl, hΦ.map_add]
    rfl
  map_smul := by
    intro c X
    ext p q
    rw [Matrix.smul_apply, amplify_apply, amplify_apply,
      show (fun i j => (c • X) (i, p.2) (j, q.2)) = c • matBlock X p.2 q.2 from rfl,
      hΦ.map_smul]
    rfl
  pos := hpos
  tp := trace_amplify hΦ.tp

/-- The amplified dilation is the dilation of the image. -/
theorem amplify_hermDilation2 {Φ : Matrix n n ℂ → Matrix n n ℂ} (hΦ : IsPositiveTP Φ)
    (X : Matrix n n ℂ) :
    amplify Φ (Fin 2) (hermDilation2 X) = hermDilation2 (Φ X) := by
  rw [hermDilation2, amplify_blockMat, hermDilation2]
  congr 1
  funext a b
  fin_cases a <;> fin_cases b <;>
    simp [hΦ.map_zero, hΦ.map_conjTranspose]

/-- **A two-positive trace-preserving map contracts the nuclear norm of every matrix.** -/
theorem nuclearNorm_apply_le_of_twoPositive {Φ : Matrix n n ℂ → Matrix n n ℂ}
    (hΦ : IsPositiveTP Φ)
    (h2 : ∀ X : Matrix (n × Fin 2) (n × Fin 2) ℂ, X.PosSemidef →
      (amplify Φ (Fin 2) X).PosSemidef)
    (X : Matrix n n ℂ) :
    finiteMatrixNuclearNorm (Φ X) ≤ finiteMatrixNuclearNorm X := by
  have hamp : IsPositiveTP (amplify Φ (Fin 2)) := isPositiveTP_amplify hΦ h2
  have hkey := hamp.nuclearNorm_apply_le_of_isHermitian (hermDilation2_isHermitian X)
  rw [amplify_hermDilation2 hΦ, finiteMatrixNuclearNorm_hermDilation2,
    finiteMatrixNuclearNorm_hermDilation2] at hkey
  linarith

/-! ## The trace norm is a norm -/

omit [Fintype n] [DecidableEq n] in
theorem hermDilation2_add (A B : Matrix n n ℂ) :
    hermDilation2 (A + B) = hermDilation2 A + hermDilation2 B := by
  ext p q
  obtain ⟨i, a⟩ := p
  obtain ⟨j, b⟩ := q
  fin_cases a <;> fin_cases b <;> simp [hermDilation2, blockMat]

theorem finiteMatrixNuclearNorm_zero {m : Type*} [Fintype m] [DecidableEq m] :
    finiteMatrixNuclearNorm (0 : Matrix m m ℂ) = 0 :=
  (finiteMatrixNuclearNorm_eq_zero_iff (0 : Matrix m m ℂ)).mpr rfl

theorem finiteMatrixNuclearNorm_neg {m : Type*} [Fintype m] [DecidableEq m]
    (X : Matrix m m ℂ) : finiteMatrixNuclearNorm (-X) = finiteMatrixNuclearNorm X := by
  rw [finiteMatrixNuclearNorm_eq_trace_sqrt_re, finiteMatrixNuclearNorm_eq_trace_sqrt_re]
  congr 2
  simp

/-- **The triangle inequality for the nuclear norm**, for arbitrary matrices: the Hermitian case
transported through the dilation, which is additive and doubles the norm. -/
theorem finiteMatrixNuclearNorm_add_le' (A B : Matrix n n ℂ) :
    finiteMatrixNuclearNorm (A + B) ≤ finiteMatrixNuclearNorm A + finiteMatrixNuclearNorm B := by
  have h := finiteMatrixNuclearNorm_add_le (hermDilation2_isHermitian A)
    (hermDilation2_isHermitian B)
  rw [← hermDilation2_add, finiteMatrixNuclearNorm_hermDilation2,
    finiteMatrixNuclearNorm_hermDilation2, finiteMatrixNuclearNorm_hermDilation2] at h
  linarith

theorem finiteMatrixNuclearNorm_sub_le' (A B : Matrix n n ℂ) :
    finiteMatrixNuclearNorm (A - B) ≤ finiteMatrixNuclearNorm A + finiteMatrixNuclearNorm B := by
  rw [sub_eq_add_neg]
  refine le_of_le_of_eq (finiteMatrixNuclearNorm_add_le' A (-B)) ?_
  rw [finiteMatrixNuclearNorm_neg]

/-- The reverse triangle inequality. -/
theorem finiteMatrixNuclearNorm_sub_le_sub (A B : Matrix n n ℂ) :
    finiteMatrixNuclearNorm A - finiteMatrixNuclearNorm B
      ≤ finiteMatrixNuclearNorm (B - A) := by
  have h : finiteMatrixNuclearNorm A ≤ finiteMatrixNuclearNorm B
      + finiteMatrixNuclearNorm (B - A) := by
    have hAB : A = B - (B - A) := by abel
    calc finiteMatrixNuclearNorm A = finiteMatrixNuclearNorm (B - (B - A)) := by rw [← hAB]
      _ ≤ finiteMatrixNuclearNorm B + finiteMatrixNuclearNorm (B - A) :=
          finiteMatrixNuclearNorm_sub_le' _ _
  linarith

theorem finiteMatrixNuclearNorm_smul_ofReal (r : ℝ) (hr : 0 ≤ r) (K : Matrix n n ℂ) :
    finiteMatrixNuclearNorm (((r : ℂ)) • K) = r * finiteMatrixNuclearNorm K := by
  have hsm : ((r : ℂ)) • K = r • K := by
    ext i j
    simp [Complex.real_smul]
  rw [hsm, finiteMatrixNuclearNorm_smul_nonneg r hr]


end

end GaloisForLFunctions.HTGeometry
