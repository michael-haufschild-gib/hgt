import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Tactic.Abel

/-!
# Projective matrices and trace-zero duality

The annihilator of trace-zero matrices is exactly the scalar line over any
commutative ring. Matrix units and diagonal differences prove this without
division by the matrix size. Consequently the radical of the trace-zero
self-pairing consists exactly of scalars killed by that size.

These are the matrix-algebra statements in Mohajer, *Semistable 1-Motives*,
Theorem 9.1 and Proposition 9.3. They also apply when trace centering by division
is unavailable. A chosen diagonal entry gives a division-free representative.
-/

namespace GaloisForLFunctions.RepresentationLifting

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

/-- The trace-zero submodule of the full matrix algebra. -/
def traceZeroMatrices (R ι : Type*) [CommRing R] [Fintype ι] :
    Submodule R (Matrix ι ι R) :=
  (Matrix.traceLinearMap ι R R).ker

/-- Scalar matrices, the ambiguity in a projective matrix. -/
def scalarMatrices (R ι : Type*) [CommRing R] [Fintype ι] [DecidableEq ι] :
    Submodule R (Matrix ι ι R) := Submodule.span R {1}

private theorem trace_single_entry (i j : ι) (c : R) :
    (Matrix.single i j c).trace = if i = j then c else 0 := by
  simpa [Matrix.one_apply, eq_comm] using
    (Matrix.trace_mul_single (1 : Matrix ι ι R) i j c)

/-- Trace-zero tests determine a matrix exactly up to a scalar identity. -/
theorem traceZero_annihilator_iff (p : ι) (A : Matrix ι ι R) :
    (∀ B : traceZeroMatrices R ι, (A * B.val).trace = 0) ↔
      ∃ c : R, A = c • (1 : Matrix ι ι R) := by
  constructor
  · intro h
    refine ⟨A p p, ?_⟩
    ext i j
    by_cases hij : i = j
    · subst j
      have hz : (Matrix.single i i (1 : R) - Matrix.single p p 1).trace = 0 := by
        rw [Matrix.trace_sub, trace_single_entry, trace_single_entry]
        simp only [↓reduceIte, sub_self]
      have hd := h ⟨_, hz⟩
      simp only [Matrix.mul_sub, Matrix.trace_sub, Matrix.trace_mul_single,
        MulOpposite.op_one, one_smul] at hd
      simpa only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
        using sub_eq_zero.mp hd
    · have hz : (Matrix.single j i (1 : R)).trace = 0 := by
        rw [trace_single_entry, if_neg (Ne.symm hij)]
      have ho := h ⟨_, hz⟩
      simpa only [Matrix.trace_mul_single, MulOpposite.op_one, one_smul,
        Matrix.smul_apply, Matrix.one_apply_ne hij, smul_zero] using ho
  · rintro ⟨c, rfl⟩ B
    rw [Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul]
    change c • B.val.trace = 0
    rw [show B.val.trace = 0 from B.property, smul_zero]

/-- Two matrices have identical trace-zero observations exactly when they differ by a scalar. -/
theorem traceZero_observations_eq_iff (p : ι) (A C : Matrix ι ι R) :
    (∀ B : traceZeroMatrices R ι, (A * B.val).trace = (C * B.val).trace) ↔
      ∃ c : R, A - C = c • (1 : Matrix ι ι R) := by
  rw [← traceZero_annihilator_iff p]
  simp only [Matrix.sub_mul, Matrix.trace_sub, sub_eq_zero]

/-- Exact radical of the trace-zero self-pairing, including torsion in the coefficient ring. -/
theorem traceZero_radical_iff (p : ι) (A : Matrix ι ι R) :
    (A.trace = 0 ∧ ∀ B : traceZeroMatrices R ι, (A * B.val).trace = 0) ↔
      ∃ c : R, c * (Fintype.card ι : R) = 0 ∧ A = c • (1 : Matrix ι ι R) := by
  rw [traceZero_annihilator_iff p]
  constructor
  · rintro ⟨ht, c, rfl⟩
    exact ⟨c, by simpa only [Matrix.trace_smul, Matrix.trace_one, smul_eq_mul] using ht,
      rfl⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨by simpa only [Matrix.trace_smul, Matrix.trace_one, smul_eq_mul] using hc,
      c, rfl⟩

/-- Subtract the pivot diagonal entry, without dividing by the matrix size. -/
def matrixPivotRepresentative (p : ι) (A : Matrix ι ι R) : Matrix ι ι R :=
  A - A p p • 1

omit [Fintype ι] in
@[simp] theorem matrixPivotRepresentative_pivot (p : ι) (A : Matrix ι ι R) :
    matrixPivotRepresentative p A p p = 0 := by
  simp [matrixPivotRepresentative]

omit [Fintype ι] in
/-- Pivot normalization respects the scalar ambiguity over every coefficient ring. -/
theorem matrixPivotRepresentative_add_scalar (p : ι) (A : Matrix ι ι R) (c : R) :
    matrixPivotRepresentative p (A + c • 1) = matrixPivotRepresentative p A := by
  simp only [matrixPivotRepresentative, Matrix.add_apply, Matrix.smul_apply,
    Matrix.one_apply_eq, smul_eq_mul, mul_one, add_smul]
  abel

omit [Fintype ι] in
/-- Pivot normalization gives a complete set of projective coordinates. -/
theorem matrixPivotRepresentative_eq_iff (p : ι) (A C : Matrix ι ι R) :
    matrixPivotRepresentative p A = matrixPivotRepresentative p C ↔
      ∃ c : R, A - C = c • (1 : Matrix ι ι R) := by
  constructor
  · intro h
    refine ⟨A p p - C p p, ?_⟩
    dsimp [matrixPivotRepresentative] at h
    rw [sub_smul]
    exact (sub_eq_sub_iff_sub_eq_sub).mp h
  · rintro ⟨c, hc⟩
    have ha : A = C + c • (1 : Matrix ι ι R) := by
      rw [← hc]
      abel
    rw [ha, matrixPivotRepresentative_add_scalar]

/-- Trace-zero measurements recover the pivot representative even in bad characteristic. -/
theorem matrixPivotRepresentative_eq_iff_observations (p : ι) (A C : Matrix ι ι R) :
    matrixPivotRepresentative p A = matrixPivotRepresentative p C ↔
      ∀ B : traceZeroMatrices R ι, (A * B.val).trace = (C * B.val).trace := by
  rw [matrixPivotRepresentative_eq_iff, traceZero_observations_eq_iff p]

/-- A projective class admits a trace-zero representative precisely when its trace
is divisible by the matrix size in the coefficient ring. -/
theorem traceZero_representative_iff (A : Matrix ι ι R) :
    (∃ c : R, (A - c • (1 : Matrix ι ι R)).trace = 0) ↔
      (Fintype.card ι : R) ∣ A.trace := by
  simp only [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, smul_eq_mul,
    sub_eq_zero, dvd_def, mul_comm]

#print axioms traceZero_annihilator_iff
#print axioms traceZero_radical_iff
#print axioms matrixPivotRepresentative_eq_iff_observations
#print axioms traceZero_representative_iff

end GaloisForLFunctions.RepresentationLifting
