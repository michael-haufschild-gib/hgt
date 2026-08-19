import GaloisForLFunctions.HTGeometry.UnipotentInverseBound

/-!
# Siegel sets in Jacobi coordinates

A Siegel set is the set of positive definite forms whose Jacobi coordinates satisfy two explicit
bounds: the diagonal grows at a controlled rate, and the unipotent part is bounded.  These are the
sets whose `SL(n, ℤ)`-translates cover the cone and which meet only finitely many of their own
translates.

* `JacobiData` : the data `(U, d)` of a Jacobi decomposition.
* `JacobiData.IsSiegel` : the two Siegel bounds.
* `JacobiData.d_le_pow` : **the diagonal bound iterated along a chain.**
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {n : ℕ}

/-- The data of a Jacobi decomposition: a unipotent upper triangular `U` and a positive diagonal. -/
structure JacobiData (n : ℕ) where
  /-- The unipotent upper triangular factor. -/
  U : Matrix (Fin n) (Fin n) ℝ
  /-- The diagonal. -/
  d : Fin n → ℝ
  /-- The diagonal is positive. -/
  pos : ∀ i, 0 < d i
  /-- `U` is upper triangular. -/
  upper : ∀ i j, j < i → U i j = 0
  /-- `U` has unit diagonal. -/
  unit : ∀ i, U i i = 1

/-- The form attached to Jacobi data. -/
def JacobiData.form (J : JacobiData n) : Matrix (Fin n) (Fin n) ℝ :=
  J.Uᵀ * Matrix.diagonal J.d * J.U

/-- Every positive definite form carries Jacobi data. -/
theorem exists_jacobiData {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) :
    ∃ J : JacobiData n, J.form = A := by
  obtain ⟨U, d, hpos, hupper, hunit, hA'⟩ := exists_jacobi_decomposition hA
  exact ⟨⟨U, d, hpos, hupper, hunit⟩, hA'.symm⟩

/-- **The Siegel bounds**: the diagonal grows at rate at most `t` along the order, and the
unipotent part has entries bounded by `u`. -/
def JacobiData.IsSiegel (J : JacobiData n) (t u : ℝ) : Prop :=
  (∀ i j : Fin n, (i : ℕ) + 1 = (j : ℕ) → J.d i ≤ t * J.d j) ∧ (∀ i j, |J.U i j| ≤ u)

/-- **The diagonal bound iterated along a chain.** -/
theorem JacobiData.d_le_pow (J : JacobiData n) {t u : ℝ} (ht : 1 ≤ t) (hS : J.IsSiegel t u) :
    ∀ k : ℕ, ∀ i j : Fin n, (j : ℕ) = (i : ℕ) + k → J.d i ≤ t ^ k * J.d j := by
  intro k
  induction k with
  | zero =>
      intro i j hij
      have : i = j := Fin.ext (by omega)
      rw [this, pow_zero, one_mul]
  | succ k ih =>
      intro i j hij
      have hlt : (i : ℕ) + 1 < n := by
        have := j.isLt
        omega
      set i' : Fin n := ⟨(i : ℕ) + 1, hlt⟩ with hi'
      have hstep : J.d i ≤ t * J.d i' := hS.1 i i' rfl
      have hrec : J.d i' ≤ t ^ k * J.d j := ih i' j (by simp only [hi']; omega)
      have ht0 : (0 : ℝ) ≤ t := le_trans zero_le_one ht
      calc J.d i ≤ t * J.d i' := hstep
        _ ≤ t * (t ^ k * J.d j) := by
            exact mul_le_mul_of_nonneg_left hrec ht0
        _ = t ^ (k + 1) * J.d j := by ring

/-- The iterated bound, stated for an ordered pair. -/
theorem JacobiData.d_le_pow_of_le (J : JacobiData n) {t u : ℝ} (ht : 1 ≤ t) (hS : J.IsSiegel t u)
    {i j : Fin n} (hij : (i : ℕ) ≤ (j : ℕ)) :
    J.d i ≤ t ^ ((j : ℕ) - (i : ℕ)) * J.d j :=
  J.d_le_pow ht hS ((j : ℕ) - (i : ℕ)) i j (by omega)

/-- On a Siegel set the diagonal ratios are bounded by a single power. -/
theorem JacobiData.d_le_pow_n (J : JacobiData n) {t u : ℝ} (ht : 1 ≤ t) (hS : J.IsSiegel t u)
    {i j : Fin n} (hij : (i : ℕ) ≤ (j : ℕ)) : J.d i ≤ t ^ n * J.d j := by
  refine le_trans (J.d_le_pow_of_le ht hS hij) ?_
  refine mul_le_mul_of_nonneg_right ?_ (le_of_lt (J.pos j))
  refine pow_le_pow_right₀ ht ?_
  have := j.isLt
  omega

end GaloisForLFunctions.HTGeometry
