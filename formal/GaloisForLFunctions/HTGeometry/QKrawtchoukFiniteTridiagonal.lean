import GaloisForLFunctions.HTGeometry.QKrawtchoukFiniteSpectralModel
import GaloisForLFunctions.HTGeometry.QKrawtchoukJacobiRealization

/-!
# The exact tridiagonal form of the finite quadrature operators

The spectral construction has the inverse-q Hermite Jacobi coefficients
on the interior block, diagonal `α - τ` at its last coordinate, and zero
on the complementary tail. Thus the boundary parameter of the quadrature
is an explicit rank-one change at the endpoint, while every fixed interior
coordinate eventually agrees with the selected infinite operator.

This identifies the actual finite operators used in the scalar-to-operator
transfer of arXiv:2609.24149 with concrete Jacobi truncations.
-/

noncomputable section
open scoped BigOperators ComplexConjugate

namespace HTGeometry

private theorem weighted_recurrence (t u w y : ℝ) (i : ℕ) :
    (w * (orthonormalPoly (inverseQHermiteMoment t u) i).eval y) * y =
      inverseQHermiteOffDiagonal t (i + 1) *
        (w * (orthonormalPoly (inverseQHermiteMoment t u) (i + 1)).eval y) +
      (Real.exp (-u) - Real.exp u) *
        (w * (orthonormalPoly (inverseQHermiteMoment t u) i).eval y) +
      inverseQHermiteOffDiagonal t i *
        (w * (orthonormalPoly (inverseQHermiteMoment t u) (i - 1)).eval y) := by
  have h := congrArg (Polynomial.eval y) (inverseQHermiteOrthonormalPoly_recurrence t u i)
  simp only [Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_add,
    Polynomial.eval_smul, smul_eq_mul] at h
  calc
    _ = w * (y * (orthonormalPoly (inverseQHermiteMoment t u) i).eval y) := by ring
    _ = _ := by rw [h]; ring

private theorem coordinate_action (t u : ℝ) (n : ℕ) (τ : ℝ) (i : Fin (n + 1)) :
    inverseQHermiteFiniteJacobiCLM t u n τ (lp.single 2 (i : ℕ) (1 : ℂ)) =
      ∑ j : Fin (n + 1), ((inverseQHermiteQuadratureMatrix t u n τ i j : ℂ) *
        (inverseQHermiteQuadratureNode t u n τ j : ℂ)) •
        inverseQHermiteFiniteVector t u n τ j := by
  rw [← inverseQHermiteFiniteVector_reconstruct t u n τ i, map_sum]
  simp only [map_smul, inverseQHermiteFiniteJacobiCLM_eigenvector, smul_smul]

/-- Every interior column has the exact infinite Jacobi coefficients. -/
theorem inverseQHermiteFiniteJacobiCLM_interior (t u : ℝ) (n : ℕ) (τ : ℝ)
    (i : Fin n) :
    inverseQHermiteFiniteJacobiCLM t u n τ (lp.single 2 (i : ℕ) (1 : ℂ)) =
      (inverseQHermiteOffDiagonal t ((i : ℕ) + 1) : ℂ) •
        lp.single 2 ((i : ℕ) + 1) (1 : ℂ) +
      ((Real.exp (-u) - Real.exp u : ℝ) : ℂ) • lp.single 2 (i : ℕ) (1 : ℂ) +
      (inverseQHermiteOffDiagonal t i : ℂ) • lp.single 2 ((i : ℕ) - 1) (1 : ℂ) := by
  let k : Fin (n + 1) := ⟨i, by omega⟩
  let ks : Fin (n + 1) := ⟨(i : ℕ) + 1, by omega⟩
  let kp : Fin (n + 1) := ⟨(i : ℕ) - 1, by omega⟩
  change inverseQHermiteFiniteJacobiCLM t u n τ (lp.single 2 (k : ℕ) (1 : ℂ)) =
    (inverseQHermiteOffDiagonal t ((i : ℕ) + 1) : ℂ) • lp.single 2 (ks : ℕ) (1 : ℂ) +
    ((Real.exp (-u) - Real.exp u : ℝ) : ℂ) • lp.single 2 (k : ℕ) (1 : ℂ) +
    (inverseQHermiteOffDiagonal t i : ℂ) • lp.single 2 (kp : ℕ) (1 : ℂ)
  rw [coordinate_action, ← inverseQHermiteFiniteVector_reconstruct t u n τ ks,
    ← inverseQHermiteFiniteVector_reconstruct t u n τ k,
    ← inverseQHermiteFiniteVector_reconstruct t u n τ kp]
  simp only [Finset.smul_sum, smul_smul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [← add_smul, ← add_smul]
  congr 1
  have h := congrArg Complex.ofReal (weighted_recurrence t u
    (Real.sqrt (inverseQHermiteQuadratureWeight t u n τ j))
    (inverseQHermiteQuadratureNode t u n τ j) i)
  simpa only [inverseQHermiteQuadratureMatrix, Complex.ofReal_mul,
    Complex.ofReal_add] using h

private theorem norm_ratio (t u : ℝ) (n : ℕ) :
    monicOrthoNorm (inverseQHermiteMoment t u) (n + 1) /
      monicOrthoNorm (inverseQHermiteMoment t u) n =
      inverseQHermiteOffDiagonal t (n + 1) := by
  rw [inverseQHermiteOffDiagonal, Nat.cast_add, Nat.cast_one, ← inverseQHermiteMoment_beta t u n,
    monicOrthoBeta, Real.sqrt_div (monicOrthoNormSq_pos
      (inverseQHermiteMoment_positive t u) (n + 1)).le]
  rfl

private theorem node_boundary (t u : ℝ) (n : ℕ) (τ : ℝ) (j : Fin (n + 1)) :
    inverseQHermiteOffDiagonal t (n + 1) *
        (orthonormalPoly (inverseQHermiteMoment t u) (n + 1)).eval
          (inverseQHermiteQuadratureNode t u n τ j) =
      -τ * (orthonormalPoly (inverseQHermiteMoment t u) n).eval
        (inverseQHermiteQuadratureNode t u n τ j) := by
  have hm := Finset.orderEmbOfFin_mem (quasiNodes (inverseQHermiteMoment t u) n τ)
    (quasiNodes_card (inverseQHermiteMoment_positive t u) n τ) j
  change inverseQHermiteQuadratureNode t u n τ j ∈
    quasiNodes (inverseQHermiteMoment t u) n τ at hm
  have hr := (mem_quasiNodes_iff n τ _).mp hm
  rw [quasiOrtho_eval] at hr
  have hroot : (monicOrtho (inverseQHermiteMoment t u) (n + 1)).eval
      (inverseQHermiteQuadratureNode t u n τ j) =
      -τ * (monicOrtho (inverseQHermiteMoment t u) n).eval
        (inverseQHermiteQuadratureNode t u n τ j) := by linarith
  rw [← norm_ratio t u n]
  simp only [orthonormalPoly, Polynomial.eval_smul, smul_eq_mul, hroot]
  field_simp [monicOrthoNorm_ne_zero (inverseQHermiteMoment_positive t u)]

/-- The quadrature parameter changes exactly the last diagonal from `α` to `α - τ`. -/
theorem inverseQHermiteFiniteJacobiCLM_boundary (t u : ℝ) (n : ℕ) (τ : ℝ) :
    inverseQHermiteFiniteJacobiCLM t u n τ (lp.single 2 n (1 : ℂ)) =
      ((Real.exp (-u) - Real.exp u - τ : ℝ) : ℂ) • lp.single 2 n (1 : ℂ) +
      (inverseQHermiteOffDiagonal t n : ℂ) • lp.single 2 (n - 1) (1 : ℂ) := by
  let k : Fin (n + 1) := ⟨n, by omega⟩
  let kp : Fin (n + 1) := ⟨n - 1, by omega⟩
  change inverseQHermiteFiniteJacobiCLM t u n τ (lp.single 2 (k : ℕ) (1 : ℂ)) =
    ((Real.exp (-u) - Real.exp u - τ : ℝ) : ℂ) • lp.single 2 (k : ℕ) (1 : ℂ) +
    (inverseQHermiteOffDiagonal t n : ℂ) • lp.single 2 (kp : ℕ) (1 : ℂ)
  rw [coordinate_action, ← inverseQHermiteFiniteVector_reconstruct t u n τ k,
    ← inverseQHermiteFiniteVector_reconstruct t u n τ kp]
  simp only [Finset.smul_sum, smul_smul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [← add_smul]
  congr 1
  have hr := weighted_recurrence t u
    (Real.sqrt (inverseQHermiteQuadratureWeight t u n τ j))
    (inverseQHermiteQuadratureNode t u n τ j) n
  have hb := node_boundary t u n τ j
  have h : inverseQHermiteQuadratureMatrix t u n τ k j *
      inverseQHermiteQuadratureNode t u n τ j =
      (Real.exp (-u) - Real.exp u - τ) * inverseQHermiteQuadratureMatrix t u n τ k j +
      inverseQHermiteOffDiagonal t n * inverseQHermiteQuadratureMatrix t u n τ kp j := by
    dsimp [inverseQHermiteQuadratureMatrix, k, kp]
    calc
      _ = _ := hr
      _ = _ := by
        rw [mul_left_comm (inverseQHermiteOffDiagonal t (n + 1)), hb]
        ring
  exact_mod_cast h

/-- The finite-rank operator vanishes on every coordinate beyond its block. -/
theorem inverseQHermiteFiniteJacobiCLM_tail (t u : ℝ) (n k : ℕ) (τ : ℝ) :
    inverseQHermiteFiniteJacobiCLM t u n τ (lp.single 2 (n + 1 + k) (1 : ℂ)) = 0 := by
  have hi (i : Fin (n + 1)) :
      inner ℂ (lp.single 2 (i : ℕ) (1 : ℂ) : lp (fun _ : ℕ => ℂ) 2)
        (lp.single 2 (n + 1 + k) (1 : ℂ)) = 0 := by
    have hne : n + 1 + k ≠ (i : ℕ) := by omega
    simp [lp.inner_single_left, lp.single_apply, hne, RCLike.inner_apply]
  have hv (j : Fin (n + 1)) : inner ℂ (inverseQHermiteFiniteVector t u n τ j)
      (lp.single 2 (n + 1 + k) (1 : ℂ)) = 0 := by
    simp only [inverseQHermiteFiniteVector, sum_inner, inner_smul_left, hi, mul_zero,
      Finset.sum_const_zero]
  rw [inverseQHermiteFiniteJacobiCLM, sum_apply]
  change (∑ j : Fin (n + 1), (inverseQHermiteQuadratureNode t u n τ j : ℂ) •
    (inner ℂ (inverseQHermiteFiniteVector t u n τ j) (lp.single 2 (n + 1 + k) (1 : ℂ)) •
      inverseQHermiteFiniteVector t u n τ j)) = 0
  simp only [hv, zero_smul, smul_zero, Finset.sum_const_zero]

end HTGeometry
