import GaloisForLFunctions.HTGeometry.MatrixLogarithmicDerivative
import GaloisForLFunctions.HTGeometry.DifferentialJacobiFormula

/-!
# Either a matrix group is constant, or its logarithmic derivatives fill the traceless matrices

The logarithmic derivative of a product is the crossed-homomorphism combination of the two, so the
span of the logarithmic derivatives of a group is stable under conjugation by the group; Jacobi's
formula puts it inside the traceless matrices as soon as the determinants are constant.

If the conjugation action leaves no proper nonzero stable subspace of the traceless matrices — the
situation for a group acting irreducibly and not inside the normaliser of a torus — the span is
therefore everything or nothing, and nothing means that every element of the group has vanishing
derivative.

That dichotomy is the group-theoretic half of the isomonodromy alternative: the logarithmic
derivatives of the Galois matrices are the conjugates of the failure of the fundamental matrix to
be isomonodromic.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Differential
open GaloisForLFunctions

variable {C : Type*} [Field C] [Differential C] {n : Type*} [Fintype n] [DecidableEq n]

/-- The logarithmic derivative of an invertible matrix. -/
def unitLogDeriv (g : (Matrix n n C)ˣ) : Matrix n n C :=
  matrixDeriv (g : Matrix n n C) * ((↑g⁻¹ : Matrix n n C))

theorem unitLogDeriv_one : unitLogDeriv (1 : (Matrix n n C)ˣ) = 0 := by
  rw [unitLogDeriv]
  show matrixDeriv (1 : Matrix n n C) * _ = 0
  rw [matrixDeriv_one, zero_mul]

/-- **The crossed-homomorphism law** for the logarithmic derivative. -/
theorem unitLogDeriv_mul (g h : (Matrix n n C)ˣ) :
    unitLogDeriv (g * h)
      = unitLogDeriv g + (g : Matrix n n C) * unitLogDeriv h * ((↑g⁻¹ : Matrix n n C)) := by
  have hmul : ((g * h : (Matrix n n C)ˣ) : Matrix n n C)
      = (g : Matrix n n C) * (h : Matrix n n C) := rfl
  have hinv : ((↑(g * h)⁻¹ : Matrix n n C))
      = ((↑h⁻¹ : Matrix n n C)) * ((↑g⁻¹ : Matrix n n C)) := by
    rw [mul_inv_rev]
    rfl
  rw [unitLogDeriv, hmul, hinv, matrixDeriv_mul, add_mul]
  congr 1
  · rw [unitLogDeriv, mul_assoc]
    congr 1
    have hhh : (h : Matrix n n C) * ((↑h⁻¹ : Matrix n n C)) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [← mul_assoc, hhh, one_mul]
  · rw [unitLogDeriv]
    rw [mul_assoc, mul_assoc, mul_assoc]

/-- The trace of the logarithmic derivative is the logarithmic derivative of the determinant. -/
theorem trace_unitLogDeriv (g : (Matrix n n C)ˣ) :
    Matrix.trace (unitLogDeriv g)
      = (Matrix.det (g : Matrix n n C))′ / Matrix.det (g : Matrix n n C) := by
  have hunit : IsUnit (Matrix.det (g : Matrix n n C)) := by
    refine (Matrix.isUnit_iff_isUnit_det _).mp ?_
    exact ⟨g, rfl⟩
  have hinv : ((↑g⁻¹ : Matrix n n C)) = (g : Matrix n n C)⁻¹ := by
    refine Matrix.inv_eq_left_inv ?_ |>.symm
    show ((↑g⁻¹ : Matrix n n C)) * (g : Matrix n n C) = 1
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [unitLogDeriv, hinv, Matrix.trace_mul_comm]
  exact trace_inv_mul_matrixDeriv (g : Matrix n n C) hunit

variable (G : Subgroup (Matrix n n C)ˣ)

/-- The span of the logarithmic derivatives of a group of invertible matrices. -/
def logDerivSpan : Submodule C (Matrix n n C) :=
  Submodule.span C (unitLogDeriv '' (G : Set ((Matrix n n C)ˣ)))

theorem mem_logDerivSpan {g : (Matrix n n C)ˣ} (hg : g ∈ G) :
    unitLogDeriv g ∈ logDerivSpan G :=
  Submodule.subset_span ⟨g, hg, rfl⟩

/-- **The span of the logarithmic derivatives is stable under conjugation by the group.** -/
theorem adjoint_mem_logDerivSpan {g : (Matrix n n C)ˣ} (hg : g ∈ G) {A : Matrix n n C}
    (hA : A ∈ logDerivSpan G) :
    (g : Matrix n n C) * A * ((↑g⁻¹ : Matrix n n C)) ∈ logDerivSpan G := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hA
  · rintro x ⟨h, hh, rfl⟩
    have hcocycle := unitLogDeriv_mul g h
    have hval : (g : Matrix n n C) * unitLogDeriv h * ((↑g⁻¹ : Matrix n n C))
        = unitLogDeriv (g * h) - unitLogDeriv g := by
      rw [hcocycle]
      abel
    rw [hval]
    exact Submodule.sub_mem _ (mem_logDerivSpan G (G.mul_mem hg hh)) (mem_logDerivSpan G hg)
  · rw [mul_zero, zero_mul]
    exact Submodule.zero_mem _
  · intro x y _ _ hx hy
    rw [mul_add, add_mul]
    exact Submodule.add_mem _ hx hy
  · intro c x _ hx
    rw [Matrix.mul_smul, Matrix.smul_mul]
    exact Submodule.smul_mem _ c hx

theorem trace_eq_zero_of_mem_logDerivSpan
    (hdet : ∀ g ∈ G, (Matrix.det (g : Matrix n n C))′ = 0)
    {A : Matrix n n C} (hA : A ∈ logDerivSpan G) : Matrix.trace A = 0 := by
  have hle : logDerivSpan G ≤ LinearMap.ker (Matrix.traceLinearMap n C C) := by
    refine Submodule.span_le.mpr ?_
    rintro x ⟨g, hg, rfl⟩
    show Matrix.trace (unitLogDeriv g) = 0
    rw [trace_unitLogDeriv, hdet g hg, zero_div]
  exact hle hA

/-- **The logarithmic derivative dichotomy.**  If the conjugation action of a group of invertible
matrices with constant determinants leaves no proper nonzero subspace of the traceless matrices
stable, then either the logarithmic derivatives fill the traceless matrices, or every element of the
group is constant. -/
theorem matrixDeriv_eq_zero_of_logDerivSpan_proper
    (hdet : ∀ g ∈ G, (Matrix.det (g : Matrix n n C))′ = 0)
    (hirr : ∀ W : Submodule C (Matrix n n C),
      (∀ g ∈ G, ∀ A ∈ W, (g : Matrix n n C) * A * ((↑g⁻¹ : Matrix n n C)) ∈ W) →
      (∀ A ∈ W, Matrix.trace A = 0) →
      W = ⊥ ∨ ∀ A : Matrix n n C, Matrix.trace A = 0 → A ∈ W)
    (hproper : ∃ A : Matrix n n C, Matrix.trace A = 0 ∧ A ∉ logDerivSpan G) :
    ∀ g ∈ G, matrixDeriv (g : Matrix n n C) = 0 := by
  rcases hirr (logDerivSpan G) (fun g hg A hA => adjoint_mem_logDerivSpan G hg hA)
      (fun A hA => trace_eq_zero_of_mem_logDerivSpan G hdet hA) with hbot | htop
  · intro g hg
    have hmem : unitLogDeriv g ∈ logDerivSpan G := mem_logDerivSpan G hg
    rw [hbot, Submodule.mem_bot] at hmem
    have hval : matrixDeriv (g : Matrix n n C) * ((↑g⁻¹ : Matrix n n C)) = 0 := hmem
    have hgg : ((↑g⁻¹ : Matrix n n C)) * (g : Matrix n n C) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    calc matrixDeriv (g : Matrix n n C)
        = matrixDeriv (g : Matrix n n C) * (((↑g⁻¹ : Matrix n n C)) * (g : Matrix n n C)) := by
          rw [hgg, mul_one]
      _ = 0 := by rw [← mul_assoc, hval, zero_mul]
  · exfalso
    obtain ⟨A, hA, hAnot⟩ := hproper
    exact hAnot (htop A hA)

end

end GaloisForLFunctions.HTGeometry
