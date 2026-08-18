import GaloisForLFunctions.HTGeometry.MatrixUnitCasimir

/-!
# From an eigenvalue gap to a quadratic-form gap

A Hermitian matrix whose nonzero eigenvalues are all at least `g` obeys the quadratic-form bound
`g‖z‖² ≤ ⟪z, Tz⟫` at every vector orthogonal to its kernel.  Expanding such a vector in an
orthonormal eigenbasis, the coefficients along kernel eigenvectors vanish, and every surviving
coefficient is weighted by an eigenvalue past `g`.

This is the exact upgrade needed to turn a spectral gap, which constrains eigenvalues one at a
time, into an operator inequality usable on a whole subspace.
-/

open scoped BigOperators Matrix

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

noncomputable section

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The coordinate inner product is the Euclidean inner product of the transported vectors. -/
theorem cinner_eq_inner (u v : X → ℂ) :
    cinner u v = inner ℂ (WithLp.toLp 2 u : EuclideanSpace ℂ X) (WithLp.toLp 2 v) := by
  rw [PiLp.inner_apply, cinner]
  simp [RCLike.inner_apply, mul_comm]

/-- The Euclidean linear map of a matrix is matrix-vector multiplication under transport. -/
theorem toEuclideanLin_toLp (M : Matrix X X ℂ) (v : X → ℂ) :
    Matrix.toEuclideanLin M (WithLp.toLp 2 v : EuclideanSpace ℂ X)
      = (WithLp.toLp 2 (M *ᵥ v) : EuclideanSpace ℂ X) := rfl

/-- **A spectral gap is a form gap off the kernel.**  If every eigenvalue of a Hermitian matrix
is either zero or at least `g`, then its quadratic form dominates `g` times the square norm at
every vector orthogonal to the kernel. -/
theorem cnormSq_le_of_eigenvalue_gap
    (T : Matrix X X ℂ) (hT : T.IsHermitian) {g : ℝ}
    (hgap : ∀ (lam : ℝ) (Y : X → ℂ), Y ≠ 0 → T *ᵥ Y = (lam : ℂ) • Y → lam = 0 ∨ g ≤ lam)
    (z : X → ℂ) (hz : ∀ w : X → ℂ, T *ᵥ w = 0 → cinner w z = 0) :
    g * cnormSq z ≤ (cinner z (T *ᵥ z)).re := by
  classical
  set b := hT.eigenvectorBasis with hb
  set mu := hT.eigenvalues with hmu
  set x : EuclideanSpace ℂ X := WithLp.toLp 2 z with hx
  set c : X → ℂ := fun j => inner ℂ (b j) x with hc
  have hmv : ∀ j, T *ᵥ ((b j).ofLp : X → ℂ) = ((mu j : ℂ)) • ((b j).ofLp : X → ℂ) := by
    intro j
    rw [hT.mulVec_eigenvectorBasis j]
    exact (RCLike.real_smul_eq_coe_smul (K := ℂ) _ _)
  have hbne : ∀ j, ((b j).ofLp : X → ℂ) ≠ 0 := by
    intro j h
    have hz0 : b j = 0 := by
      have hh : (WithLp.toLp 2 ((b j).ofLp) : EuclideanSpace ℂ X)
          = WithLp.toLp 2 (0 : X → ℂ) := by rw [h]
      simpa using hh
    have hnorm := b.orthonormal.1 j
    rw [hz0] at hnorm
    simp at hnorm
  have hdich : ∀ j, mu j = 0 ∨ g ≤ mu j := fun j => hgap (mu j) _ (hbne j) (hmv j)
  have hcform : ∀ j, c j = cinner ((b j).ofLp : X → ℂ) z := by
    intro j
    rw [hc, cinner_eq_inner]
  have hczero : ∀ j, mu j = 0 → c j = 0 := by
    intro j hj
    rw [hcform j]
    refine hz _ ?_
    have hj0 : ((mu j : ℝ) : ℂ) = 0 := by rw [hj]; simp
    rw [hmv j, hj0, zero_smul]
  have hrepr : ∀ j, (b.repr x).ofLp j = c j := fun j => b.repr_apply_apply x j
  have hpar : cnormSq z = ∑ j, ‖c j‖ ^ 2 := by
    have h4 : cinner z z = ((cnormSq z : ℝ) : ℂ) := cinner_self z
    have h1 : cinner z z = inner ℂ x x := by rw [cinner_eq_inner]
    have h2 : inner ℂ x x = inner ℂ (b.repr x) (b.repr x) :=
      (LinearIsometryEquiv.inner_map_map b.repr x x).symm
    have h3 : inner ℂ (b.repr x) (b.repr x) = ((∑ j, ‖c j‖ ^ 2 : ℝ) : ℂ) := by
      rw [PiLp.inner_apply, Complex.ofReal_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hrepr j]
      simp only [RCLike.inner_apply]
      rw [Complex.mul_conj']
      push_cast
      ring
    have h5 : ((cnormSq z : ℝ) : ℂ) = ((∑ j, ‖c j‖ ^ 2 : ℝ) : ℂ) := by
      rw [← h4, h1, h2, h3]
    exact_mod_cast h5
  have hform : (cinner z (T *ᵥ z)).re = ∑ j, mu j * ‖c j‖ ^ 2 := by
    have hsym : (Matrix.toEuclideanLin T).IsSymmetric :=
      Matrix.isSymmetric_toEuclideanLin_iff.mpr hT
    have hTx : Matrix.toEuclideanLin T x = WithLp.toLp 2 (T *ᵥ z) := toEuclideanLin_toLp T z
    have hreprT : ∀ j, (b.repr (Matrix.toEuclideanLin T x)).ofLp j = ((mu j : ℂ)) * c j := by
      intro j
      rw [b.repr_apply_apply]
      have hTb : Matrix.toEuclideanLin T (b j) = ((mu j : ℂ)) • b j := by
        have hstep : Matrix.toEuclideanLin T (WithLp.toLp 2 ((b j).ofLp) : EuclideanSpace ℂ X)
            = WithLp.toLp 2 (T *ᵥ ((b j).ofLp)) := toEuclideanLin_toLp T _
        simp only [WithLp.toLp_ofLp] at hstep
        rw [hstep, hmv j]
        rfl
      rw [← hsym (b j) x, hTb, inner_smul_left]
      simp [hc]
    have h1 : cinner z (T *ᵥ z) = inner ℂ x (Matrix.toEuclideanLin T x) := by
      rw [cinner_eq_inner, hTx]
    have h2 : inner ℂ x (Matrix.toEuclideanLin T x)
        = inner ℂ (b.repr x) (b.repr (Matrix.toEuclideanLin T x)) :=
      (LinearIsometryEquiv.inner_map_map b.repr _ _).symm
    have h3 : inner ℂ (b.repr x) (b.repr (Matrix.toEuclideanLin T x))
        = ((∑ j, mu j * ‖c j‖ ^ 2 : ℝ) : ℂ) := by
      rw [PiLp.inner_apply, Complex.ofReal_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hrepr j, hreprT j]
      simp only [RCLike.inner_apply]
      rw [show ((mu j : ℝ) : ℂ) * c j * (starRingEnd ℂ) (c j)
          = ((mu j : ℝ) : ℂ) * (c j * (starRingEnd ℂ) (c j)) by ring, Complex.mul_conj']
      push_cast
      ring
    rw [h1, h2, h3, Complex.ofReal_re]
  rw [hpar, hform, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rcases hdich j with h | h
  · rw [hczero j h, h]
    simp
  · exact mul_le_mul_of_nonneg_right h (sq_nonneg _)

end

end GaloisForLFunctions.HTGeometry
