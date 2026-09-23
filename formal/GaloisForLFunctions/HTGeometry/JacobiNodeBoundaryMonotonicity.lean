import GaloisForLFunctions.HTGeometry.JacobiTodaRiccatiLaw
import GaloisForLFunctions.HTGeometry.MatrixInverseCurveDerivative

/-!
# The boundary channel seen by a single Gauss node

An irreducible Jacobi matrix has no eigenvector with vanishing last coordinate: reading the
eigenvalue equation from the bottom row upwards, a zero last coordinate propagates to every
coordinate.  Consequently every node sees the boundary port.

Combined with the vanishing of the Rayleigh quotient of a commutator at an eigenvector and with
the derivative law of a differentiable eigenvalue branch, this turns a rank-one positive boundary
source in a matrix Riccati flow into strict monotonicity of every simple eigenvalue.
-/

open Finset Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-! ## The rows of a Jacobi compression -/

/-- Every row past the first of a tridiagonal band is a three-term sum. -/
theorem jacobiRow_sum_succ (a b : ℕ → ℝ) (g : ℕ → ℝ) (i N : ℕ) (hN : i + 3 ≤ N) :
    ∑ l ∈ Finset.range N, jacobiEntry a b (i + 1) l * g l
      = a (i + 1) * g i + b (i + 1) * g (i + 1) + a (i + 2) * g (i + 2) := by
  have hsub : Finset.range (i + 3) ⊆ Finset.range N := fun x hx =>
    Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) hN)
  have hzero : ∀ l ∈ Finset.range N, l ∉ Finset.range (i + 3) →
      jacobiEntry a b (i + 1) l * g l = 0 := by
    intro l _ hl
    simp only [Finset.mem_range, not_lt] at hl
    rw [jacobiEntry_of_lt a b (by omega : i + 1 + 1 < l), zero_mul]
  rw [← Finset.sum_subset hsub hzero]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
  have hlow : ∑ l ∈ Finset.range i, jacobiEntry a b (i + 1) l * g l = 0 := by
    refine Finset.sum_eq_zero fun l hl => ?_
    simp only [Finset.mem_range] at hl
    rw [jacobiEntry_of_gt a b (by omega : l + 1 < i + 1), zero_mul]
  rw [hlow, zero_add, jacobiEntry_succ' a b i, jacobiEntry_diag a b (i + 1),
    jacobiEntry_succ a b (i + 1)]

/-! ## No eigenvector of an irreducible Jacobi compression sees a silent boundary -/

/-- **The boundary port is visible to every node.**  An eigenvector of a Jacobi compression with
nonvanishing off-diagonal band has nonzero last coordinate. -/
theorem jacobiCompression_eigenvector_last_ne_zero (a b : ℕ → ℝ) (m : ℕ)
    (ha : ∀ k, 1 ≤ k → k ≤ m → a k ≠ 0) {lam : ℝ} {x : Fin (m + 1) → ℝ}
    (hx : jacobiCompression a b (m + 1) *ᵥ x = lam • x) (hne : x ≠ 0) :
    x (Fin.last m) ≠ 0 := by
  intro hlast
  apply hne
  classical
  set g : ℕ → ℝ := fun j => if h : j < m + 1 then x ⟨j, h⟩ else 0 with hgdef
  have hgx : ∀ i : Fin (m + 1), g (i : ℕ) = x i := by
    intro i
    simp only [hgdef, dif_pos i.isLt]
  have hgz : ∀ j, m < j → g j = 0 := by
    intro j hj
    simp only [hgdef, dif_neg (by omega : ¬ j < m + 1)]
  have hgm : g m = 0 := by
    have := hgx (Fin.last m)
    simpa [Fin.val_last, hlast] using this
  -- the row equations, transported to `ℕ`
  have hrow : ∀ i, i + 1 ≤ m →
      a (i + 1) * g i + b (i + 1) * g (i + 1) + a (i + 2) * g (i + 2) = lam * g (i + 1) := by
    intro i hi
    have hidx : i + 1 < m + 1 := by omega
    have hval := congrFun hx ⟨i + 1, hidx⟩
    have hlhs : (jacobiCompression a b (m + 1) *ᵥ x) ⟨i + 1, hidx⟩
        = ∑ l ∈ Finset.range (m + 2), jacobiEntry a b (i + 1) l * g l := by
      have h1 : (jacobiCompression a b (m + 1) *ᵥ x) ⟨i + 1, hidx⟩
          = ∑ j : Fin (m + 1), jacobiEntry a b (i + 1) (j : ℕ) * g (j : ℕ) := by
        simp only [Matrix.mulVec, dotProduct, jacobiCompression, Matrix.of_apply]
        exact Finset.sum_congr rfl fun j _ => by rw [hgx j]
      rw [h1, Fin.sum_univ_eq_sum_range (fun l => jacobiEntry a b (i + 1) l * g l) (m + 1)]
      refine Finset.sum_subset (fun l hl =>
        Finset.mem_range.mpr (by have := Finset.mem_range.mp hl; omega)) ?_
      intro l _ hl
      simp only [Finset.mem_range, not_lt] at hl
      rw [hgz l (by omega), mul_zero]
    rw [hlhs, jacobiRow_sum_succ a b g i (m + 2) (by omega)] at hval
    rw [hval]
    simp [hgx ⟨i + 1, hidx⟩]
  -- descending induction from the boundary
  have hQ : ∀ k j, m ≤ j + k → g j = 0 := by
    intro k
    induction k with
    | zero =>
        intro j hj
        rcases eq_or_lt_of_le hj with h | h
        · have hjm : j = m := by omega
          rw [hjm]; exact hgm
        · exact hgz j (by omega)
    | succ k ih =>
        intro j hj
        by_cases hk : m ≤ j + k
        · exact ih j hk
        · have hjm : j + k + 1 = m := by omega
          have h1 : g (j + 1) = 0 := ih (j + 1) (by omega)
          have h2 : g (j + 2) = 0 := ih (j + 2) (by omega)
          have hr := hrow j (by omega)
          rw [h1, h2] at hr
          have hane : a (j + 1) ≠ 0 := ha (j + 1) (by omega) (by omega)
          have : a (j + 1) * g j = 0 := by linarith
          rcases mul_eq_zero.mp this with h | h
          · exact absurd h hane
          · exact h
  funext i
  rw [Pi.zero_apply, ← hgx i]
  exact hQ m (i : ℕ) (by omega)

/-! ## A commutator is invisible to an eigenvector -/

/-- The Rayleigh quotient of a commutator with a symmetric matrix vanishes at every eigenvector of
that matrix. -/
theorem dotProduct_commutator_eigenvector {n : ℕ} {U A : Matrix (Fin n) (Fin n) ℝ}
    {lam : ℝ} {x : Fin n → ℝ} (hsym : Uᵀ = U) (heig : U *ᵥ x = lam • x) :
    x ⬝ᵥ ((U * A - A * U) *ᵥ x) = 0 := by
  have h1 : x ⬝ᵥ ((U * A) *ᵥ x) = lam * (x ⬝ᵥ (A *ᵥ x)) := by
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← hsym, Matrix.vecMul_transpose, heig,
      smul_dotProduct, smul_eq_mul]
  have h2 : x ⬝ᵥ ((A * U) *ᵥ x) = lam * (x ⬝ᵥ (A *ᵥ x)) := by
    rw [← Matrix.mulVec_mulVec, heig, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
  rw [Matrix.sub_mulVec, dotProduct_sub, h1, h2, sub_self]

/-! ## The derivative of a differentiable eigenvalue branch -/

theorem hasDerivAt_finsetSum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ) (f' : ι → ℝ) {y : ℝ}
    (h : ∀ i ∈ s, HasDerivAt (f i) (f' i) y) :
    HasDerivAt (fun v => ∑ i ∈ s, f i v) (∑ i ∈ s, f' i) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hasDerivAt_const y (0 : ℝ)
  | insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact (h a (by simp)).add (ih fun i hi => h i (by simp [hi]))

/-- **The eigenvalue derivative law.**  A differentiable unit eigenvector branch of a symmetric
matrix curve moves its eigenvalue by exactly the Rayleigh quotient of the matrix velocity. -/
theorem eigenvalue_hasDerivAt_eq_rayleigh {n : ℕ} {U : ℝ → Matrix (Fin n) (Fin n) ℝ}
    {U' : Matrix (Fin n) (Fin n) ℝ} {x : ℝ → (Fin n → ℝ)} {x' : Fin n → ℝ}
    {u : ℝ → ℝ} {u' y : ℝ}
    (hU : MatrixHasDerivAt U U' y) (hx : ∀ i, HasDerivAt (fun v => x v i) (x' i) y)
    (hu : HasDerivAt u u' y) (heig : ∀ v, U v *ᵥ x v = u v • x v)
    (hnorm : ∀ v, x v ⬝ᵥ x v = 1) (hsym : (U y)ᵀ = U y) :
    u' = x y ⬝ᵥ (U' *ᵥ x y) := by
  -- the eigenvalue is the Rayleigh quotient
  have hq : ∀ v, u v = ∑ i, ∑ j, x v i * (U v i j * x v j) := by
    intro v
    have h1 : x v ⬝ᵥ (U v *ᵥ x v) = ∑ i, ∑ j, x v i * (U v i j * x v j) := by
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    have h2 : x v ⬝ᵥ (U v *ᵥ x v) = u v := by
      rw [heig v, dotProduct_smul, smul_eq_mul, hnorm v, mul_one]
    rw [← h2, h1]
  -- differentiate the Rayleigh quotient
  have hd : HasDerivAt (fun v => ∑ i, ∑ j, x v i * (U v i j * x v j))
      (∑ i, ∑ j, (x' i * (U y i j * x y j)
        + x y i * (U' i j * x y j + U y i j * x' j))) y := by
    refine hasDerivAt_finsetSum _ _ _ fun i _ => ?_
    refine hasDerivAt_finsetSum _ _ _ fun j _ => ?_
    exact (hx i).mul ((hU i j).mul (hx j))
  have hufun : u = fun v => ∑ i, ∑ j, x v i * (U v i j * x v j) := funext hq
  rw [hufun] at hu
  have hval := hu.unique hd
  -- split the three groups of terms
  have e1 : x' ⬝ᵥ (U y *ᵥ x y) = ∑ i, ∑ j, x' i * (U y i j * x y j) := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  have e2 : x y ⬝ᵥ (U' *ᵥ x y) = ∑ i, ∑ j, x y i * (U' i j * x y j) := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  have e3 : x y ⬝ᵥ (U y *ᵥ x') = ∑ i, ∑ j, x y i * (U y i j * x' j) := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  have hstep : ∀ i j : Fin n, x' i * (U y i j * x y j)
        + x y i * (U' i j * x y j + U y i j * x' j)
      = x' i * (U y i j * x y j) + x y i * (U' i j * x y j) + x y i * (U y i j * x' j) := by
    intro i j; ring
  have hsplit : (∑ i, ∑ j, (x' i * (U y i j * x y j)
        + x y i * (U' i j * x y j + U y i j * x' j)))
      = (x' ⬝ᵥ (U y *ᵥ x y)) + (x y ⬝ᵥ (U' *ᵥ x y)) + (x y ⬝ᵥ (U y *ᵥ x')) := by
    simp only [hstep, Finset.sum_add_distrib]
    rw [e1, e2, e3]
  -- the eigenvector stays orthogonal to its own velocity
  have hperp : x' ⬝ᵥ x y = 0 := by
    have hone : HasDerivAt (fun v => ∑ i, x v i * x v i) 0 y := by
      have hc : (fun v => ∑ i, x v i * x v i) = fun _ : ℝ => (1 : ℝ) := by
        funext v
        simpa [dotProduct] using hnorm v
      rw [hc]
      exact hasDerivAt_const y 1
    have hd2 : HasDerivAt (fun v => ∑ i, x v i * x v i)
        (∑ i, (x' i * x y i + x y i * x' i)) y :=
      hasDerivAt_finsetSum _ _ _ fun i _ => (hx i).mul (hx i)
    have h0 := hd2.unique hone
    have hcomm : ∑ i, x y i * x' i = ∑ i, x' i * x y i :=
      Finset.sum_congr rfl fun i _ => mul_comm _ _
    have hsum : (∑ i, (x' i * x y i + x y i * x' i)) = 2 * (x' ⬝ᵥ x y) := by
      rw [Finset.sum_add_distrib, hcomm]
      simp only [dotProduct]
      ring
    rw [hsum] at h0
    linarith
  have h1 : x' ⬝ᵥ (U y *ᵥ x y) = 0 := by
    rw [heig y, dotProduct_smul, smul_eq_mul, hperp, mul_zero]
  have h2 : x y ⬝ᵥ (U y *ᵥ x') = 0 := by
    rw [Matrix.dotProduct_mulVec, ← hsym, Matrix.vecMul_transpose, heig y,
      smul_dotProduct, smul_eq_mul, dotProduct_comm, hperp, mul_zero]
  rw [hval, hsplit, h1, h2, zero_add, add_zero]

/-- The Rayleigh quotient of a scaled rank-one square. -/
theorem dotProduct_smul_vecMulVec_eq {n : ℕ} (c : ℝ) (w x : Fin n → ℝ) :
    x ⬝ᵥ ((c • Matrix.vecMulVec w w) *ᵥ x) = c * (x ⬝ᵥ w) ^ (2 : ℕ) := by
  simp [Matrix.mulVec, Matrix.vecMulVec_apply, dotProduct, Finset.mul_sum,
    mul_comm, mul_left_comm, sq]

end GaloisForLFunctions.HTGeometry
