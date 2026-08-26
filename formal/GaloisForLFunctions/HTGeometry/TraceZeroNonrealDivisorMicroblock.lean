import GaloisForLFunctions.HTGeometry.FiniteRankDeterminantCompletion

/-!
# Arbitrarily small trace-zero nonreal divisor microblocks

Exact trace cancellation and Hilbert--Schmidt smallness do not control finite Fredholm divisors.
The diagonal block `diag(ai,-ai)` has trace zero and a nonreal zero at `-i/a`.  Its norm tends to
zero with `a`, while that zero escapes to infinity.  This is the sharp local mechanism by which
nonreal finite-stage divisors remain invisible to compact-open completion.
-/

open Complex Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Two-dimensional trace-zero block with imaginary eigenvalues `ai` and `-ai`. -/
def traceZeroImaginaryMicroblock (a : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(a : ℂ) * I, 0; 0, -((a : ℂ) * I)]

/-- Kernel presentation used by the Hilbert--Schmidt determinant infrastructure. -/
def traceZeroImaginaryMicrokernel (a : ℝ) : (Fin 2 × Fin 2) → ℂ :=
  fun p => traceZeroImaginaryMicroblock a p.1 p.2

theorem isHS_traceZeroImaginaryMicrokernel (a : ℝ) :
    HilbertSchmidt.IsHS (traceZeroImaginaryMicrokernel a) :=
  Summable.of_finite

theorem hsTraceDiag_traceZeroImaginaryMicrokernel (a : ℝ) :
    HilbertSchmidt.hsTraceDiag (traceZeroImaginaryMicrokernel a) = 0 := by
  rw [HilbertSchmidt.hsTraceDiag, tsum_fintype, Fin.sum_univ_two]
  simp [traceZeroImaginaryMicrokernel, traceZeroImaginaryMicroblock]

theorem hsNormSq_traceZeroImaginaryMicrokernel (a : ℝ) :
    HilbertSchmidt.hsNormSq (traceZeroImaginaryMicrokernel a) = 2 * a ^ 2 := by
  rw [HilbertSchmidt.hsNormSq, tsum_fintype]
  simp [Fintype.sum_prod_type, Fin.sum_univ_two, traceZeroImaginaryMicrokernel,
    traceZeroImaginaryMicroblock, Complex.norm_real]
  ring

/-- The first imaginary eigenvalue gives the explicit nonreal Fredholm zero `-i/a`. -/
theorem traceZeroImaginaryMicroblock_det_zero {a : ℝ} (ha : a ≠ 0) :
    ((1 : Matrix (Fin 2) (Fin 2) ℂ) -
      (-(I : ℂ) / (a : ℂ)) • traceZeroImaginaryMicroblock a).det = 0 := by
  rw [Matrix.det_fin_two]
  simp [traceZeroImaginaryMicroblock]
  left
  field_simp
  simp [Complex.I_sq, ha]

theorem traceZeroImaginaryMicroblock_root_im_ne_zero {a : ℝ} (ha : a ≠ 0) :
    (-(I : ℂ) / (a : ℂ)).im ≠ 0 := by
  simp [ha]

/-- Arbitrarily small finite-support trace-zero kernels can retain a nonreal ordinary-determinant
zero.  Smallness only forces that zero to escape compact spectral apertures. -/
theorem exists_arbitrarilySmall_traceZero_nonrealDivisorMicroblock :
    ∀ ε : ℝ, 0 < ε →
      ∃ (M : Matrix (Fin 2) (Fin 2) ℂ) (z : ℂ),
        HilbertSchmidt.IsHS (fun p => M p.1 p.2) ∧
        HilbertSchmidt.hsTraceDiag (fun p => M p.1 p.2) = 0 ∧
        HilbertSchmidt.hsNorm (fun p => M p.1 p.2) < ε ∧
        ((1 : Matrix (Fin 2) (Fin 2) ℂ) - z • M).det = 0 ∧
        z.im ≠ 0 := by
  intro ε hε
  let a : ℝ := ε / 4
  have ha : 0 < a := by dsimp [a]; positivity
  refine ⟨traceZeroImaginaryMicroblock a, -(I : ℂ) / (a : ℂ), ?_⟩
  constructor
  · change HilbertSchmidt.IsHS (traceZeroImaginaryMicrokernel a)
    exact isHS_traceZeroImaginaryMicrokernel a
  constructor
  · change HilbertSchmidt.hsTraceDiag (traceZeroImaginaryMicrokernel a) = 0
    exact hsTraceDiag_traceZeroImaginaryMicrokernel a
  constructor
  · change HilbertSchmidt.hsNorm (traceZeroImaginaryMicrokernel a) < ε
    rw [HilbertSchmidt.hsNorm, hsNormSq_traceZeroImaginaryMicrokernel]
    have hsqrt : Real.sqrt (2 * a ^ 2) ≤ 2 * a := by
      apply (Real.sqrt_le_iff).2
      constructor
      · positivity
      · nlinarith
    calc
      Real.sqrt (2 * a ^ 2) ≤ 2 * a := hsqrt
      _ < ε := by dsimp [a]; linarith
  constructor
  · exact traceZeroImaginaryMicroblock_det_zero ha.ne'
  · exact traceZeroImaginaryMicroblock_root_im_ne_zero ha.ne'

end
end GaloisForLFunctions.HTGeometry
