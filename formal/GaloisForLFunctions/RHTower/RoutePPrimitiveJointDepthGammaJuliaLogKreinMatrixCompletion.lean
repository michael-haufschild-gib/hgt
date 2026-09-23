import GaloisForLFunctions.RHTower.RoutePPrimitiveJointDepthGammaJuliaScalarIntertwinerNoGo
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Route P joint-depth Gamma--Julia log-Krein matrix completion

P-G105E proves that literal joint-depth source and co-source are related by prime-log diagonal,
not a scalar.  This file carries that survivor through arbitrary finite off-diagonal incidence.

For a packet of `(prime, depth)` labels, let

```text
L = diag(log p_i).
```

Every source Gram `G` becomes `L G L` in co-source coordinates.  Completing with P-G105C's
universal Julia--Krein block `B` gives

```text
K = B tensor (L G L).
```

Entrywise, every original incidence `G_ij` is retained with exact Radon--Nikodym weight
`log(p_i)log(p_j)`.  Since every prime logarithm is positive and `det(B)=-1`,

```text
det K = (-1)^N det(L)^(4 : ℕ) det(G)^(2 : ℕ),
```

so operator-valued completion creates and hides no finite degeneracy.  This also constructs the
corresponding log-conjugated P-G186 matrix, but does not claim the P-G186 half-line features have
already been identified with literal joint-depth Xi vectors.  Signed bivariate stability, Stokes
orientation, cofinal sewing, and Xi divisor equality remain separate gates.
-/

open Complex Matrix Set
open scoped Kronecker

namespace RHTower

noncomputable section

/-- Prime-log Radon--Nikodym diagonal on a finite joint-depth packet. -/
def routePPrimitiveJointDepthPrimeLogDiagonal {N : ℕ}
    (pe : Fin N → Nat.Primes × ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.diagonal (fun i => (Real.log (pe i).1 : ℂ))

/-- Operator-valued source Gram in literal reciprocal-promotion co-source coordinates. -/
def routePPrimitiveJointDepthPrimeLogConjugate {N : ℕ}
    (pe : Fin N → Nat.Primes × ℕ) (G : Matrix (Fin N) (Fin N) ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  routePPrimitiveJointDepthPrimeLogDiagonal pe * G *
    routePPrimitiveJointDepthPrimeLogDiagonal pe

/-- Exact retention of every off-diagonal incidence under prime-log conjugation. -/
theorem routePPrimitiveJointDepthPrimeLogConjugate_apply {N : ℕ}
    (pe : Fin N → Nat.Primes × ℕ) (G : Matrix (Fin N) (Fin N) ℂ)
    (i j : Fin N) :
    routePPrimitiveJointDepthPrimeLogConjugate pe G i j =
      (Real.log (pe i).1 : ℂ) * G i j *
        (Real.log (pe j).1 : ℂ) := by
  rw [routePPrimitiveJointDepthPrimeLogConjugate,
    routePPrimitiveJointDepthPrimeLogDiagonal,
    Matrix.mul_diagonal, Matrix.diagonal_mul]

/-- Julia--Krein completion after retaining primitive-promotion prime logs. -/
def routePPrimitiveJointDepthGammaJuliaLogKreinCompletedMatrix {N : ℕ}
    (pe : Fin N → Nat.Primes × ℕ) (G : Matrix (Fin N) (Fin N) ℂ) :
    Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℂ :=
  routePPrimitiveBurnolJuliaKreinBlock ⊗ₖ
    routePPrimitiveJointDepthPrimeLogConjugate pe G

/-- Determinant of the prime-log diagonal is the product of literal prime logarithms. -/
theorem routePPrimitiveJointDepthPrimeLogDiagonal_det {N : ℕ}
    (pe : Fin N → Nat.Primes × ℕ) :
    (routePPrimitiveJointDepthPrimeLogDiagonal pe).det =
      ∏ i, (Real.log (pe i).1 : ℂ) := by
  rw [routePPrimitiveJointDepthPrimeLogDiagonal, Matrix.det_diagonal]

/-- Every finite prime-log diagonal is invertible, without distinct-label assumptions. -/
theorem routePPrimitiveJointDepthPrimeLogDiagonal_det_ne_zero {N : ℕ}
    (pe : Fin N → Nat.Primes × ℕ) :
    (routePPrimitiveJointDepthPrimeLogDiagonal pe).det ≠ 0 := by
  rw [routePPrimitiveJointDepthPrimeLogDiagonal_det]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _hi
  exact Complex.ofReal_ne_zero.mpr
    (Real.log_pos (by exact_mod_cast (pe i).1.property.one_lt)).ne'

/-- Exact determinant cost of converting co-source coordinates to primitive source coordinates. -/
theorem routePPrimitiveJointDepthPrimeLogConjugate_det {N : ℕ}
    (pe : Fin N → Nat.Primes × ℕ) (G : Matrix (Fin N) (Fin N) ℂ) :
    (routePPrimitiveJointDepthPrimeLogConjugate pe G).det =
      (routePPrimitiveJointDepthPrimeLogDiagonal pe).det ^ (2 : ℕ) * G.det := by
  rw [routePPrimitiveJointDepthPrimeLogConjugate,
    Matrix.det_mul, Matrix.det_mul]
  ring

/-- **P-G105F determinant law.** Full operator-valued Julia--Krein completion retains source
determinant squared and pays exactly fourth power of primitive-promotion Jacobian. -/
theorem routePPrimitiveJointDepthGammaJuliaLogKreinCompletedMatrix_det {N : ℕ}
    (pe : Fin N → Nat.Primes × ℕ) (G : Matrix (Fin N) (Fin N) ℂ) :
    (routePPrimitiveJointDepthGammaJuliaLogKreinCompletedMatrix pe G).det =
      (-1 : ℂ) ^ N *
        (routePPrimitiveJointDepthPrimeLogDiagonal pe).det ^ (4 : ℕ) *
        G.det ^ (2 : ℕ) := by
  rw [routePPrimitiveJointDepthGammaJuliaLogKreinCompletedMatrix,
    Matrix.det_kronecker,
    routePPrimitiveBurnolJuliaKreinBlock_det,
    routePPrimitiveJointDepthPrimeLogConjugate_det]
  simp only [Fintype.card_fin]
  ring

/-- Prime-log operator-valued completion is nondegenerate exactly when original finite Gram is. -/
theorem routePPrimitiveJointDepthGammaJuliaLogKreinCompletedMatrix_det_ne_zero_iff
    {N : ℕ} (pe : Fin N → Nat.Primes × ℕ)
    (G : Matrix (Fin N) (Fin N) ℂ) :
    (routePPrimitiveJointDepthGammaJuliaLogKreinCompletedMatrix pe G).det ≠ 0 ↔
      G.det ≠ 0 := by
  rw [routePPrimitiveJointDepthGammaJuliaLogKreinCompletedMatrix_det]
  have hL := routePPrimitiveJointDepthPrimeLogDiagonal_det_ne_zero pe
  simp [hL]

/-- P-G186 specialization of the required prime-log operator-valued completion. -/
def routePPrimitiveBurnolGammaJuliaLogKreinCompletedMatrix {N : ℕ}
    (pe : Fin N → Nat.Primes × ℕ) (kappa : Fin N → ℝ) :
    Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℂ :=
  routePPrimitiveJointDepthGammaJuliaLogKreinCompletedMatrix pe
    (routePPrimitiveBurnolWindowGramMatrix pe kappa)

/-- Exact determinant of the log-conjugated P-G186 completion. -/
theorem routePPrimitiveBurnolGammaJuliaLogKreinCompletedMatrix_det {N : ℕ}
    (pe : Fin N → Nat.Primes × ℕ) (kappa : Fin N → ℝ) :
    (routePPrimitiveBurnolGammaJuliaLogKreinCompletedMatrix pe kappa).det =
      (-1 : ℂ) ^ N *
        (routePPrimitiveJointDepthPrimeLogDiagonal pe).det ^ (4 : ℕ) *
        (routePPrimitiveBurnolWindowGramMatrix pe kappa).det ^ (2 : ℕ) := by
  exact routePPrimitiveJointDepthGammaJuliaLogKreinCompletedMatrix_det pe _

/-- P-G105F capstone: exact operator-valued full-matrix law, determinant, and degeneracy
classification, with no hypotheses on packet or source Gram. -/
theorem routePPrimitiveJointDepth_GammaJulia_logKreinMatrixCompletion {N : ℕ}
    (pe : Fin N → Nat.Primes × ℕ) (G : Matrix (Fin N) (Fin N) ℂ) :
    routePPrimitiveJointDepthGammaJuliaLogKreinCompletedMatrix pe G =
        routePPrimitiveBurnolJuliaKreinBlock ⊗ₖ
          routePPrimitiveJointDepthPrimeLogConjugate pe G ∧
      (routePPrimitiveJointDepthGammaJuliaLogKreinCompletedMatrix pe G).det =
        (-1 : ℂ) ^ N *
          (routePPrimitiveJointDepthPrimeLogDiagonal pe).det ^ (4 : ℕ) *
          G.det ^ (2 : ℕ) ∧
      ((routePPrimitiveJointDepthGammaJuliaLogKreinCompletedMatrix pe G).det ≠ 0 ↔
        G.det ≠ 0) :=
  ⟨rfl,
    routePPrimitiveJointDepthGammaJuliaLogKreinCompletedMatrix_det pe G,
    routePPrimitiveJointDepthGammaJuliaLogKreinCompletedMatrix_det_ne_zero_iff pe G⟩

end
end RHTower
