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
  have hfun : h = fun j ⇒ ∑ k, x k * c k j := by
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

/-- A linearly independent pair whose second normalized Gram--Schmidt vector has a nonzero first
original-coordinate component. -/
def ryazanovOriginalPair : Fin 2 → ℝ × ℝ := ![(1, 0), (1, 1)]

/-- The normalized Gram--Schmidt family of `ryazanovOriginalPair`. -/
def ryazanovOrthonormalPair : Fin 2 → ℝ × ℝ := ![(1, 0), (0, 1)]

theorem ryazanovOriginalPair_linearIndependent :
    LinearIndependent ℝ ryazanovOriginalPair := by
  rw [linearIndependent_iff_injective_fintypeLinearCombination]
  intro x y hxy
  simp only [Fintype.linearCombination_apply, Fin.sum_univ_two, ryazanovOriginalPair,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, smul_eq_mul,
    Prod.smul_mk] at hxy
  apply funext
  intro i
  fin_cases i
  · exact congrArg Prod.fst hxy
  · have hsecond := congrArg Prod.snd hxy
    simpa using sub_eq_sub_iff_add_eq_add.mp (sub_eq_sub_iff_left.mpr hsecond)

theorem ryazanovOrthonormalPair_orthonormal :
    Orthonormal ℝ ryazanovOrthonormalPair := by
  rw [orthonormal_iff_ite]
  intro i j
  fin_cases i <;> fin_cases j <;> simp [ryazanovOrthonormalPair]

/-- The displayed family is exactly Mathlib's normalized Gram--Schmidt output for the original
pair, rather than merely an unrelated orthonormal basis. -/
theorem gramSchmidtNormed_ryazanovOriginalPair :
    gramSchmidtNormed ℝ ryazanovOriginalPair = ryazanovOrthonormalPair := by
  funext i
  fin_cases i
  · simp [gramSchmidtNormed, ryazanovOrthonormalPair, ryazanovOriginalPair]
  · ext <;>
      norm_num [gramSchmidtNormed, ryazanovOrthonormalPair, ryazanovOriginalPair,
        gramSchmidt_def, Submodule.starProjection]

/-- The second normalized Gram--Schmidt vector equals `a₁ - a₀`, so its coefficient on the
first original vector is `-1`. -/
theorem ryazanovOrthonormalPair_triangular :
    ryazanovOrthonormalPair 0 = ryazanovOriginalPair 0 ∧
      ryazanovOrthonormalPair 1 = ryazanovOriginalPair 1 - ryazanovOriginalPair 0 := by
  constructor <;> ext <;> simp [ryazanovOrthonormalPair, ryazanovOriginalPair]

/-- Explicit failure of the coordinate substitution: the second orthonormal vector has zero
inner product with the first one but contributes the nonzero coefficient `-1` to the first
original-basis coordinate. -/
theorem ryazanov_coordinateMixing_counterexample :
    ryazanovOrthonormalPair 1 =
        (-1 : ℝ) • ryazanovOriginalPair 0 + 1 • ryazanovOriginalPair 1 ∧
      ⟪ryazanovOrthonormalPair 1, ryazanovOrthonormalPair 0⟫_ℝ = 0 ∧
      (-1 : ℝ) ≠ 0 := by
  constructor
  · ext <;> simp [ryazanovOrthonormalPair, ryazanovOriginalPair]
  · exact ⟨by simp [ryazanovOrthonormalPair], by norm_num⟩

end GaloisForLFunctions.RHTower
