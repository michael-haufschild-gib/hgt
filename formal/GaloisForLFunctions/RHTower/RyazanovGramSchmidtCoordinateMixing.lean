import GaloisForLFunctions.HTGeometry.GramDeterminantDistance

/-!
# Gram--Schmidt coordinates mix the original basis

This module isolates the change-of-basis error in Ryazanov's proposed contradiction.  If an
orthonormal family is triangular in an original linearly independent family, then the first
original-basis coefficient of an orthogonal projection receives a contribution from every later
orthonormal vector.  An explicit two-dimensional Gram--Schmidt family shows that this contribution
need not vanish.
-/

open scoped BigOperators InnerProductSpace
open InnerProductSpace

namespace GaloisForLFunctions.RHTower

variable {K E : Type*} [RCLike K] [NormedAddCommGroup E] [InnerProductSpace K E]

noncomputable section

/-- Substituting a finite change of basis and exchanging the two finite sums gives the exact
coefficient packet in the original family.  Triangularity is not needed for this algebraic
identity; it only identifies which terms can occur in applications. -/
theorem changeOfBasis_sum {n : ℕ}
    (a e : Fin n → E) (c : Fin n → Fin n → K)
    (he : ∀ k, e k = ∑ j, c k j • a j) (x : Fin n → K) :
    ∑ k, x k • e k = ∑ j, (∑ k, x k * c k j) • a j := by
  simp_rw [he, Finset.smul_sum, smul_smul, Finset.sum_smul]
  rw [Finset.sum_comm]

/-- Uniqueness in the linearly independent original family identifies every original-basis
coefficient after a finite change of basis. -/
theorem coordinate_eq_sum_changeOfBasis {n : ℕ}
    (a e : Fin n → E) (c : Fin n → Fin n → K)
    (ha : LinearIndependent K a)
    (he : ∀ k, e k = ∑ j, c k j • a j)
    (x h : Fin n → K)
    (hexp : ∑ k, x k • e k = ∑ j, h j • a j) (j : Fin n) :
    h j = ∑ k, x k * c k j := by
  have hfun : h = fun j ↦ ∑ k, x k * c k j := by
    apply ha.fintypeLinearCombination_injective
    simp only [Fintype.linearCombination_apply]
    rw [← hexp, changeOfBasis_sum a e c he x]
  exact congrFun hfun j

/-- The coefficient of `a j` in a finite orthogonal projection is the sum of the `a j`
components of every orthonormal vector, weighted by its projection coefficient. -/
theorem projection_originalCoordinate {n : ℕ}
    (a e : Fin n → E) (c : Fin n → Fin n → K)
    (ha : LinearIndependent K a)
    (he : ∀ k, e k = ∑ j, c k j • a j)
    (chi : E) (h : Fin n → K)
    (hexp : ∑ k, ⟪chi, e k⟫_K • e k = ∑ j, h j • a j) (j : Fin n) :
    h j = ∑ k, ⟪chi, e k⟫_K * c k j :=
  coordinate_eq_sum_changeOfBasis a e c ha he _ h hexp j

/-- For a normalized first Gram--Schmidt vector, the first original coefficient is its expected
first-vector term plus the contributions of all later orthonormal vectors. -/
theorem projection_firstOriginalCoordinate {n : ℕ}
    (a e : Fin (n + 1) → E) (c : Fin (n + 1) → Fin (n + 1) → K)
    (ha : LinearIndependent K a)
    (he : ∀ k, e k = ∑ j, c k j • a j)
    (chi : E) (h : Fin (n + 1) → K)
    (hexp : ∑ k, ⟪chi, e k⟫_K • e k = ∑ j, h j • a j)
    (hc : c 0 0 = (‖a 0‖ : K)⁻¹) :
    h 0 = ⟪chi, e 0⟫_K / (‖a 0‖ : K) +
      ∑ k : Fin n, ⟪chi, e k.succ⟫_K * c k.succ 0 := by
  rw [projection_originalCoordinate a e c ha he chi h hexp 0, Fin.sum_univ_succ, hc,
    div_eq_mul_inv]

/-! ## A concrete Gram--Schmidt counterexample -/

/-- The standard orthonormal pair in two-dimensional Euclidean space. -/
def ryazanovOrthonormalPair : Fin 2 → EuclideanSpace ℝ (Fin 2) :=
  fun i ↦ EuclideanSpace.single i 1

/-- A linearly independent pair whose second normalized Gram--Schmidt vector has a nonzero first
original-coordinate component. -/
def ryazanovOriginalPair : Fin 2 → EuclideanSpace ℝ (Fin 2) :=
  ![ryazanovOrthonormalPair 0, ryazanovOrthonormalPair 0 + ryazanovOrthonormalPair 1]

theorem ryazanovOriginalPair_linearIndependent :
    LinearIndependent ℝ ryazanovOriginalPair := by
  rw [linearIndependent_iff_injective_fintypeLinearCombination]
  intro x y hxy
  have hcoord (i : Fin 2) :=
    congrArg (fun v : EuclideanSpace ℝ (Fin 2) ↦ v i) hxy
  simp only [Fintype.linearCombination_apply, Fin.sum_univ_two, ryazanovOriginalPair,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    ryazanovOrthonormalPair, PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply] at hcoord
  funext i
  fin_cases i
  · have h0 := hcoord 0
    have h1 := hcoord 1
    norm_num at h0 h1 ⊢
    linarith
  · have h1 := hcoord 1
    norm_num at h1 ⊢
    exact h1

theorem ryazanovOrthonormalPair_orthonormal :
    Orthonormal ℝ ryazanovOrthonormalPair := by
  exact EuclideanSpace.orthonormal_single

/-- The displayed family is exactly Mathlib's normalized Gram--Schmidt output for the original
pair, rather than merely an unrelated orthonormal basis. -/
theorem gramSchmidtNormed_ryazanovOriginalPair :
    gramSchmidtNormed ℝ ryazanovOriginalPair = ryazanovOrthonormalPair := by
  have hgs0 : gramSchmidt ℝ ryazanovOriginalPair 0 = ryazanovOriginalPair 0 := by
    have hIio : Finset.Iio (0 : Fin 2) = ∅ := by
      ext i
      fin_cases i <;> simp
    rw [gramSchmidt_def]
    simp [hIio]
  have hgs1 : gramSchmidt ℝ ryazanovOriginalPair 1 = ryazanovOrthonormalPair 1 := by
    have hIio : Finset.Iio (1 : Fin 2) = {0} := by
      ext i
      fin_cases i <;> simp
    have h := gramSchmidt_def'' ℝ ryazanovOriginalPair (1 : Fin 2)
    rw [hIio] at h
    simp only [Finset.sum_singleton] at h
    rw [hgs0] at h
    apply add_right_cancel (b := ryazanovOriginalPair 0)
    simpa [ryazanovOriginalPair, ryazanovOrthonormalPair,
      EuclideanSpace.inner_single_left, add_comm] using h.symm
  funext i
  fin_cases i
  · change gramSchmidtNormed ℝ ryazanovOriginalPair 0 = ryazanovOrthonormalPair 0
    rw [gramSchmidtNormed, hgs0]
    simp [ryazanovOrthonormalPair, ryazanovOriginalPair]
  · change gramSchmidtNormed ℝ ryazanovOriginalPair 1 = ryazanovOrthonormalPair 1
    rw [gramSchmidtNormed, hgs1]
    simp [ryazanovOrthonormalPair]

/-- The second normalized Gram--Schmidt vector equals `a₁ - a₀`, so its coefficient on the
first original vector is `-1`. -/
theorem ryazanovOrthonormalPair_triangular :
    ryazanovOrthonormalPair 0 = ryazanovOriginalPair 0 ∧
      ryazanovOrthonormalPair 1 = ryazanovOriginalPair 1 - ryazanovOriginalPair 0 := by
  constructor <;> ext i <;> fin_cases i <;>
    simp [ryazanovOrthonormalPair, ryazanovOriginalPair]

/-- Explicit failure of the coordinate substitution: the second orthonormal vector has zero
inner product with the first one but contributes the nonzero coefficient `-1` to the first
original-basis coordinate. -/
theorem ryazanov_coordinateMixing_counterexample :
    ryazanovOrthonormalPair 1 =
        (-1 : ℝ) • ryazanovOriginalPair 0 + 1 • ryazanovOriginalPair 1 ∧
      ⟪ryazanovOrthonormalPair 1, ryazanovOrthonormalPair 0⟫_ℝ = 0 ∧
      (-1 : ℝ) ≠ 0 := by
  constructor
  · ext i
    fin_cases i <;> simp [ryazanovOrthonormalPair, ryazanovOriginalPair]
  · exact ⟨by simp [ryazanovOrthonormalPair, EuclideanSpace.inner_single_left], by norm_num⟩

end

end GaloisForLFunctions.RHTower
