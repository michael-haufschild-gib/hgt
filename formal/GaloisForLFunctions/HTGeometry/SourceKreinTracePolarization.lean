import GaloisForLFunctions.HTGeometry.NonlocalSourceChiralPolarization

/-!
# Hyperbolic Krein polarization preserving every source trace

Hermitian dilation replaces holomorphic power traces by Gram energies.  Hyperbolic doubling does
not.  For a finite source matrix `C`, put

`K(C) = diag(C, Cᴴ)` and `J = [[0,1],[1,0]]`.

Then `K(C)` is exactly `J`-self-adjoint.  The positive-chirality weight recovers every source
power trace, while the full determinant is the Schwarz double of the source determinant.  Scaling
`J` produces an escaping nondegenerate polarization without changing the adjoint law.

Thus Krein doubling solves signed-trace retention exactly.  Its unavoidable cost is also exact:
the full divisor is conjugation-closed, not real-axis supported.  Selecting one chirality restores
the original source divisor rather than moving it.
-/

open Complex Matrix
open scoped Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Hyperbolic double of a finite source matrix. -/
def sourceKreinDouble (C : Matrix ι ι ℂ) :
    Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ :=
  Matrix.fromBlocks C 0 0 Cᴴ

/-- Fundamental hyperbolic exchange polarization. -/
def sourceKreinSwap : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ :=
  Matrix.fromBlocks 0 1 1 0

/-- Positive-chirality weight.  Weighted traces see the original source block exactly. -/
def sourceKreinChiralWeight : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ :=
  Matrix.fromBlocks 1 0 0 0

/-- Escaping Krein polarization. -/
def sourceEscapingKreinMetric (k : ℕ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ :=
  (((k : ℝ) + 1 : ℝ) : ℂ) • sourceKreinSwap

omit [DecidableEq ι] in
theorem sourceBlockDiagonal_mul (A B D E : Matrix ι ι ℂ) :
    Matrix.fromBlocks A 0 0 D * Matrix.fromBlocks B 0 0 E =
      Matrix.fromBlocks (A * B) 0 0 (D * E) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp only [Matrix.mul_apply, Fintype.sum_sum_type]
  all_goals simp [Matrix.mul_apply]

@[simp] theorem sourceKreinSwap_conjTranspose :
    (sourceKreinSwap : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ)ᴴ = sourceKreinSwap := by
  simp [sourceKreinSwap, Matrix.fromBlocks_conjTranspose]

@[simp] theorem sourceKreinSwap_sq :
    (sourceKreinSwap : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) * sourceKreinSwap = 1 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [sourceKreinSwap, Matrix.mul_apply, Matrix.one_apply]

/-- Hyperbolic doubling is genuinely Krein self-adjoint for every source matrix. -/
theorem sourceKreinDouble_metricAdjoint (C : Matrix ι ι ℂ) :
    sourceKreinSwap * sourceKreinDouble C =
      (sourceKreinDouble C)ᴴ * sourceKreinSwap := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [sourceKreinSwap, sourceKreinDouble, Matrix.mul_apply, Matrix.one_apply]

/-- The escaping rescaling preserves exact Krein self-adjointness. -/
theorem sourceEscapingKreinMetric_metricAdjoint (k : ℕ) (C : Matrix ι ι ℂ) :
    sourceEscapingKreinMetric k * sourceKreinDouble C =
      (sourceKreinDouble C)ᴴ * sourceEscapingKreinMetric k := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [sourceEscapingKreinMetric, sourceKreinSwap, sourceKreinDouble,
      Matrix.mul_apply, Matrix.one_apply, mul_comm]

/-- Exact coercive escape: absolute squared polarization is `(k+1)² I`. -/
theorem sourceEscapingKreinMetric_absSq (k : ℕ) :
    (sourceEscapingKreinMetric k : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ)ᴴ *
        sourceEscapingKreinMetric k =
      ((((k : ℝ) + 1) ^ 2 : ℝ) : ℂ) • 1 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [sourceEscapingKreinMetric, sourceKreinSwap,
      Matrix.mul_apply, Matrix.one_apply, eq_comm]
  all_goals ring

/-- Powers remain block diagonal. -/
theorem sourceKreinDouble_pow (C : Matrix ι ι ℂ) (m : ℕ) :
    (sourceKreinDouble C) ^ m =
      Matrix.fromBlocks (C ^ m) 0 0 ((Cᴴ) ^ m) := by
  induction m with
  | zero =>
      ext i j
      rcases i with i | i <;> rcases j with j | j <;>
        simp [sourceKreinDouble, Matrix.one_apply]
  | succ m ih =>
      rw [pow_succ, ih]
      unfold sourceKreinDouble
      rw [sourceBlockDiagonal_mul]
      simp only [pow_succ]

/-- Every holomorphic source power trace, including the quadratic trace, survives exactly. -/
theorem sourceKreinChiralWeight_trace_pow (C : Matrix ι ι ℂ) (m : ℕ) :
    (sourceKreinChiralWeight * (sourceKreinDouble C) ^ m).trace =
      (C ^ m).trace := by
  rw [sourceKreinDouble_pow]
  have hmul : sourceKreinChiralWeight *
      Matrix.fromBlocks (C ^ m) 0 0 ((Cᴴ) ^ m) =
        Matrix.fromBlocks (C ^ m) 0 0 0 := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [sourceKreinChiralWeight, Matrix.mul_apply, Matrix.one_apply]
  rw [hmul]
  simp [Matrix.trace]

/-- Full Krein divisor is product of source and adjoint-source divisors. -/
theorem sourceKreinDouble_det_factor (C : Matrix ι ι ℂ) (z : ℂ) :
    ((1 : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) - z • sourceKreinDouble C).det =
      ((1 : Matrix ι ι ℂ) - z • C).det *
        ((1 : Matrix ι ι ℂ) - z • Cᴴ).det := by
  have hblock : (1 : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) - z • sourceKreinDouble C =
      Matrix.fromBlocks ((1 : Matrix ι ι ℂ) - z • C) 0 0
        ((1 : Matrix ι ι ℂ) - z • Cᴴ) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [sourceKreinDouble, Matrix.one_apply]
  rw [hblock]
  exact Matrix.det_fromBlocks_zero₁₂ _ _ _

/-- Exact Schwarz-square form of the full Krein determinant. -/
theorem sourceKreinDouble_det_eq_source_mul_reflected
    (C : Matrix ι ι ℂ) (z : ℂ) :
    ((1 : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) - z • sourceKreinDouble C).det =
      ((1 : Matrix ι ι ℂ) - z • C).det *
        (starRingEnd ℂ)
          (((1 : Matrix ι ι ℂ) - (starRingEnd ℂ) z • C).det) := by
  rw [sourceKreinDouble_det_factor]
  congr 1
  rw [show (1 : Matrix ι ι ℂ) - z • Cᴴ =
      ((1 : Matrix ι ι ℂ) - (starRingEnd ℂ) z • C)ᴴ by
    ext i j
    simp [Matrix.one_apply, eq_comm]]
  exact Matrix.det_conjTranspose _

end

end GaloisForLFunctions.HTGeometry
