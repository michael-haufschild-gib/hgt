import GaloisForLFunctions.HTGeometry.FiniteNuclearIncidenceLaw

/-!
# The trace norm of a Hermitian matrix and its duality

The nuclear (trace) norm of a Hermitian matrix is the sum of the absolute values of its
eigenvalues.  This module proves that identification and the variational description that goes
with it:

`‖A‖₁ = max { Re tr(A Y) : Y Hermitian, -1 ≤ Y ≤ 1 }`.

Both halves are elementary consequences of the spectral theorem: the upper bound because the
diagonal entries of a Hermitian contraction lie in `[-1,1]`, and the attainment because the sign
of the spectrum, conjugated back, is itself a Hermitian contraction.

The duality is what makes the trace norm usable: the triangle inequality is immediate from it, and
so is the contractivity of a positive trace-preserving map, because the adjoint of such a map is
positive and unital and therefore preserves the set of Hermitian contractions.
-/

open Matrix
open scoped Matrix ComplexOrder MatrixOrder BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The trace of a continuous functional calculus image of a Hermitian matrix is the sum of the
values of the function on the spectrum. -/
theorem trace_cfc_re {A : Matrix n n ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (cfc f A).trace.re = ∑ i, f (hA.eigenvalues i) := by
  rw [hA.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply,
    Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, Matrix.one_mul, Matrix.trace_diagonal]
  simp [Function.comp_def]

/-- The positive square root of `A²` is the functional calculus absolute value of `A`. -/
theorem cfc_abs_eq_sqrt {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    CFC.sqrt (Aᴴ * A) = cfc (fun x : ℝ => |x|) A := by
  have hcont : ContinuousOn (fun x : ℝ => |x|) (spectrum ℝ A) :=
    (continuous_abs).continuousOn
  have hsq : cfc (fun x : ℝ => |x|) A * cfc (fun x : ℝ => |x|) A = Aᴴ * A := by
    rw [← cfc_mul (fun x : ℝ => |x|) (fun x : ℝ => |x|) A hcont hcont]
    have : (fun x : ℝ => |x| * |x|) = fun x : ℝ => x * x := by
      funext x; rw [abs_mul_abs_self]
    rw [this, cfc_mul (R := ℝ) (fun x : ℝ => x) (fun x : ℝ => x) A
      (continuous_id.continuousOn) (continuous_id.continuousOn)]
    have hid : cfc (fun x : ℝ => x) A = A := cfc_id ℝ A hA.isSelfAdjoint
    rw [hid, hA.eq]
  exact CFC.sqrt_unique hsq (cfc_nonneg fun x _ => abs_nonneg x)

/-- **The nuclear norm of a Hermitian matrix is the absolute eigenvalue sum.** -/
theorem finiteMatrixNuclearNorm_isHermitian {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    finiteMatrixNuclearNorm A = ∑ i, |hA.eigenvalues i| := by
  rw [finiteMatrixNuclearNorm_eq_trace_sqrt_re, cfc_abs_eq_sqrt hA, trace_cfc_re hA]

/-- The real trace of a Hermitian matrix is the eigenvalue sum. -/
theorem trace_re_eq_sum_eigenvalues {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    A.trace.re = ∑ i, hA.eigenvalues i := by
  have hid : cfc (fun x : ℝ => x) A = A := cfc_id ℝ A hA.isSelfAdjoint
  have := trace_cfc_re hA (fun x : ℝ => x)
  rwa [hid] at this

/-- **A positive semidefinite matrix has nuclear norm its trace.** -/
theorem finiteMatrixNuclearNorm_posSemidef {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    finiteMatrixNuclearNorm A = A.trace.re := by
  rw [finiteMatrixNuclearNorm_isHermitian hA.isHermitian, trace_re_eq_sum_eigenvalues hA.isHermitian]
  exact Finset.sum_congr rfl fun i _ => abs_of_nonneg (hA.eigenvalues_nonneg i)

/-- A Hermitian Loewner contraction: a self-adjoint matrix squeezed between `-1` and `1`. -/
structure IsHermContraction (Y : Matrix n n ℂ) : Prop where
  isHermitian : Y.IsHermitian
  neg_one_le : -1 ≤ Y
  le_one : Y ≤ 1

omit [Fintype n] in
/-- The diagonal entries of a Hermitian contraction have real part in `[-1,1]`. -/
theorem IsHermContraction.abs_re_diag_le {Y : Matrix n n ℂ} (hY : IsHermContraction Y) (i : n) :
    |(Y i i).re| ≤ 1 := by
  have hupper : ((1 : Matrix n n ℂ) - Y).PosSemidef := Matrix.le_iff.mp hY.le_one
  have hlower : (Y - (-1 : Matrix n n ℂ)).PosSemidef := Matrix.le_iff.mp hY.neg_one_le
  have h1 : (0 : ℂ) ≤ ((1 : Matrix n n ℂ) - Y) i i := hupper.diag_nonneg
  have h2 : (0 : ℂ) ≤ (Y - (-1 : Matrix n n ℂ)) i i := hlower.diag_nonneg
  have e1 : ((1 : Matrix n n ℂ) - Y) i i = 1 - Y i i := by simp [Matrix.sub_apply, Matrix.one_apply_eq]
  have e2 : (Y - (-1 : Matrix n n ℂ)) i i = Y i i + 1 := by
    simp [Matrix.sub_apply, Matrix.one_apply_eq, sub_neg_eq_add]
  rw [e1] at h1
  rw [e2] at h2
  have h1' : (0 : ℝ) ≤ (1 - Y i i).re := by
    simpa using (Complex.le_def.mp h1).1
  have h2' : (0 : ℝ) ≤ (Y i i + 1).re := by
    simpa using (Complex.le_def.mp h2).1
  simp only [Complex.sub_re, Complex.one_re, Complex.add_re] at h1' h2'
  rw [abs_le]
  constructor <;> linarith

/-- Unitary conjugation preserves Hermitian contractions. -/
theorem IsHermContraction.conj {Y U : Matrix n n ℂ} (hY : IsHermContraction Y)
    (hU : U ∈ unitary (Matrix n n ℂ)) : IsHermContraction (Uᴴ * Y * U) := by
  have hstar : star U = Uᴴ := rfl
  have hUU : Uᴴ * U = 1 := by
    have := hU.1
    rwa [hstar] at this
  refine ⟨?_, ?_, ?_⟩
  · show (Uᴴ * Y * U)ᴴ = Uᴴ * Y * U
    simp [Matrix.conjTranspose_mul, hY.isHermitian.eq, Matrix.mul_assoc]
  · rw [Matrix.le_iff]
    have h : Uᴴ * Y * U - (-1 : Matrix n n ℂ) = Uᴴ * (Y - (-1 : Matrix n n ℂ)) * U := by
      rw [Matrix.mul_sub, Matrix.sub_mul]
      simp [hUU]
    rw [h]
    exact (Matrix.le_iff.mp hY.neg_one_le).conjTranspose_mul_mul_same U
  · rw [Matrix.le_iff]
    have h : (1 : Matrix n n ℂ) - Uᴴ * Y * U = Uᴴ * ((1 : Matrix n n ℂ) - Y) * U := by
      rw [Matrix.mul_sub, Matrix.sub_mul]
      simp [hUU]
    rw [h]
    exact (Matrix.le_iff.mp hY.le_one).conjTranspose_mul_mul_same U

/-- The spectral factorisation in the form used below. -/
theorem hermitian_eq_conj_diagonal {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    A = (hA.eigenvectorUnitary : Matrix n n ℂ)
        * Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues)
        * (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ := by
  conv_lhs => rw [hA.spectral_theorem]
  rw [Unitary.conjStarAlgAut_apply]
  rfl

/-- **Duality, the upper bound.**  Every Hermitian contraction pairs with a Hermitian matrix at
most as strongly as its nuclear norm. -/
theorem re_trace_mul_le_nuclearNorm {A Y : Matrix n n ℂ} (hA : A.IsHermitian)
    (hY : IsHermContraction Y) : ((A * Y).trace).re ≤ finiteMatrixNuclearNorm A := by
  classical
  set U : Matrix n n ℂ := (hA.eigenvectorUnitary : Matrix n n ℂ) with hUdef
  have hUmem : U ∈ unitary (Matrix n n ℂ) := hA.eigenvectorUnitary.2
  set D : Matrix n n ℂ := Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) with hDdef
  set Z : Matrix n n ℂ := Uᴴ * Y * U with hZdef
  have hZ : IsHermContraction Z := hY.conj hUmem
  have hAeq : A = U * D * Uᴴ := hermitian_eq_conj_diagonal hA
  have htr : (A * Y).trace = (D * Z).trace := by
    rw [hAeq, show U * D * Uᴴ * Y = U * (D * Uᴴ * Y) by simp [Matrix.mul_assoc],
      Matrix.trace_mul_comm]
    congr 1
    simp [hZdef, Matrix.mul_assoc]
  have hsum : (D * Z).trace = ∑ i, (RCLike.ofReal (hA.eigenvalues i) : ℂ) * Z i i := by
    rw [Matrix.trace]
    exact Finset.sum_congr rfl fun i _ => by
      simp [hDdef, Matrix.diagonal_mul, Matrix.diag]
  rw [htr, hsum, Complex.re_sum, finiteMatrixNuclearNorm_isHermitian hA]
  refine Finset.sum_le_sum fun i _ => ?_
  have hre : ((RCLike.ofReal (hA.eigenvalues i) : ℂ) * Z i i).re
      = hA.eigenvalues i * (Z i i).re := by
    simp [Complex.mul_re]
  rw [hre]
  have hbound := hZ.abs_re_diag_le i
  have : hA.eigenvalues i * (Z i i).re ≤ |hA.eigenvalues i * (Z i i).re| := le_abs_self _
  refine this.trans ?_
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) hbound

/-- **Duality, the attainment.**  The sign of the spectrum, conjugated back, is a Hermitian
contraction realising the nuclear norm. -/
theorem exists_isHermContraction_re_trace_eq {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    ∃ Y : Matrix n n ℂ, IsHermContraction Y ∧
      ((A * Y).trace).re = finiteMatrixNuclearNorm A := by
  classical
  set U : Matrix n n ℂ := (hA.eigenvectorUnitary : Matrix n n ℂ) with hUdef
  have hUmem : U ∈ unitary (Matrix n n ℂ) := hA.eigenvectorUnitary.2
  have hUUH : Uᴴ * U = 1 := by
    have := hUmem.1
    simpa [Matrix.star_eq_conjTranspose] using this
  have hUUH' : U * Uᴴ = 1 := by
    have := hUmem.2
    simpa [Matrix.star_eq_conjTranspose] using this
  have hUH : Uᴴ ∈ unitary (Matrix n n ℂ) := by
    refine ⟨?_, ?_⟩
    · show star Uᴴ * Uᴴ = 1
      simpa [Matrix.star_eq_conjTranspose] using hUUH'
    · show Uᴴ * star Uᴴ = 1
      simpa [Matrix.star_eq_conjTranspose] using hUUH
  set D : Matrix n n ℂ := Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) with hDdef
  set sgn : n → ℝ := fun i => if 0 ≤ hA.eigenvalues i then 1 else -1 with hsgndef
  set S : Matrix n n ℂ := Matrix.diagonal (fun i => (sgn i : ℂ)) with hSdef
  have hSherm : S.IsHermitian := by
    show Sᴴ = S
    rw [hSdef, Matrix.diagonal_conjTranspose]
    simp
  have hScontr : IsHermContraction S := by
    refine ⟨hSherm, ?_, ?_⟩
    · rw [Matrix.le_iff]
      have : S - (-1 : Matrix n n ℂ) = Matrix.diagonal (fun i => ((sgn i + 1 : ℝ) : ℂ)) := by
        ext i j
        by_cases h : i = j <;>
          simp [hSdef, Matrix.sub_apply, h]
      rw [this, Matrix.posSemidef_diagonal_iff]
      intro i
      have : (0 : ℝ) ≤ sgn i + 1 := by
        rw [hsgndef]; dsimp only; split <;> norm_num
      exact_mod_cast Complex.zero_le_real.mpr this
    · rw [Matrix.le_iff]
      have : (1 : Matrix n n ℂ) - S = Matrix.diagonal (fun i => ((1 - sgn i : ℝ) : ℂ)) := by
        ext i j
        by_cases h : i = j <;>
          simp [hSdef, Matrix.sub_apply, h]
      rw [this, Matrix.posSemidef_diagonal_iff]
      intro i
      have : (0 : ℝ) ≤ 1 - sgn i := by
        rw [hsgndef]; dsimp only; split <;> norm_num
      exact_mod_cast Complex.zero_le_real.mpr this
  refine ⟨U * S * Uᴴ, ?_, ?_⟩
  · have := hScontr.conj hUH
    simpa [Matrix.conjTranspose_conjTranspose] using this
  · have hAeq : A = U * D * Uᴴ := hermitian_eq_conj_diagonal hA
    have hcancel : Uᴴ * (U * S * Uᴴ) = S * Uᴴ := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hUUH, Matrix.one_mul]
    have hkey : U * D * Uᴴ * (U * S * Uᴴ) = U * ((D * S) * Uᴴ) := by
      calc U * D * Uᴴ * (U * S * Uᴴ) = U * D * (Uᴴ * (U * S * Uᴴ)) := by rw [Matrix.mul_assoc]
        _ = U * D * (S * Uᴴ) := by rw [hcancel]
        _ = U * ((D * S) * Uᴴ) := by simp [Matrix.mul_assoc]
    have htr : (A * (U * S * Uᴴ)).trace = (D * S).trace := by
      rw [hAeq, hkey, Matrix.trace_mul_comm, Matrix.mul_assoc, hUUH, Matrix.mul_one]
    rw [htr, finiteMatrixNuclearNorm_isHermitian hA]
    have hsum : (D * S).trace = ∑ i, ((hA.eigenvalues i * sgn i : ℝ) : ℂ) := by
      rw [Matrix.trace]
      exact Finset.sum_congr rfl fun i _ => by
        simp [hDdef, hSdef, Matrix.diag, Matrix.diagonal_apply_eq]
    rw [hsum, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : hA.eigenvalues i * sgn i = |hA.eigenvalues i| := by
      rw [hsgndef]
      dsimp only
      split
      · rw [mul_one, abs_of_nonneg (by assumption)]
      · rw [mul_neg_one, abs_of_neg (by linarith [not_le.mp (by assumption : ¬ 0 ≤ hA.eigenvalues i)])]
    simp [this]

/-- **The triangle inequality for the nuclear norm of Hermitian matrices.** -/
theorem finiteMatrixNuclearNorm_add_le {A B : Matrix n n ℂ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) :
    finiteMatrixNuclearNorm (A + B) ≤ finiteMatrixNuclearNorm A + finiteMatrixNuclearNorm B := by
  obtain ⟨Y, hY, hYeq⟩ := exists_isHermContraction_re_trace_eq (hA.add hB)
  rw [← hYeq, Matrix.add_mul, Matrix.trace_add, Complex.add_re]
  exact add_le_add (re_trace_mul_le_nuclearNorm hA hY) (re_trace_mul_le_nuclearNorm hB hY)

end

end GaloisForLFunctions.HTGeometry
