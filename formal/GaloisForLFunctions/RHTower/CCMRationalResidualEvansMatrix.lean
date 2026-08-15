import GaloisForLFunctions.HTGeometry.CharacteristicModeDimension

/-!
# The reconstructed rational residual has an exact finite Evans matrix

Four exact mechanisms of the card are formalized.

*The residual space is `2 L`-dimensional.*  `R_L = span {x^j e^{x}, x^j e^{-x} : j < L}` is the
smooth solution space of `(D - 1)^L (D + 1)^L`, so `CharacteristicModeDimension` gives its dimension
exactly: `2 L`.  Every listed mode is in it, and it is spanned by them.

*The cross-boundary block lands in `R_L`.*  For an interior point `x` and a right exterior point
`y` one has `|x - y| = y - x`, so the Bessel tail `e^{-|x-y|} Q(|x-y|)` expands, for `deg Q < L`, as
`∑_{j<L} α_j(y) x^j e^{x}` — equation `(11)`.  Reflection gives `(12)` with `x^j e^{-x}`.

*The Bessel tail is stable under differentiation.*  `(e^{-t} Q(t))' = e^{-t} (Q' - Q)(t)` and
`deg (Q' - Q) ≤ deg Q`, which is `(10)`.

*The finite Gram criterion.*  For the coordinate matrix `A` of the residual map, `Gram = Aᴴ A`
satisfies `⟪x, Gram x⟫ = ‖A x‖²`, and `A` is injective iff `Gram` is positive definite iff
`det Gram > 0` — equations `(7)` and `(15)`.

The unbounded logarithmic Dirichlet inverse `C_{a,I}^{-1}`, the identification of `k_L` as the
inverse Fourier transform of `(1+ξ²)^{-L}`, and the endpoint distributions of `(13)` are cited
analytic parents and stay outside the Lean statement.
-/

open Complex Matrix

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

open scoped ComplexOrder

/-! ## The residual space `R_L` -/

/-- The characteristic polynomial of the residual space, `(D-1)^L (D+1)^L`. -/
def residualPoly (L : ℕ) : Polynomial ℂ :=
  (Polynomial.X - Polynomial.C 1) ^ L * (Polynomial.X - Polynomial.C (-1)) ^ L

theorem residualPoly_ne_zero (L : ℕ) : residualPoly L ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ (Polynomial.X_sub_C_ne_zero _))
    (pow_ne_zero _ (Polynomial.X_sub_C_ne_zero _))

theorem natDegree_residualPoly (L : ℕ) : (residualPoly L).natDegree = 2 * L := by
  rw [residualPoly, Polynomial.natDegree_mul (pow_ne_zero _ (Polynomial.X_sub_C_ne_zero _))
    (pow_ne_zero _ (Polynomial.X_sub_C_ne_zero _)), Polynomial.natDegree_pow,
    Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, Polynomial.natDegree_X_sub_C]
  ring

theorem rootMultiplicity_residualPoly_one (L : ℕ) :
    (residualPoly L).rootMultiplicity 1 = L := by
  have hne : ¬ (((Polynomial.X - Polynomial.C (-1)) ^ L : Polynomial ℂ)).IsRoot 1 := by
    rw [Polynomial.IsRoot]
    simp only [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    refine pow_ne_zero _ ?_
    norm_num
  rw [residualPoly, Polynomial.rootMultiplicity_mul (residualPoly_ne_zero L),
    Polynomial.rootMultiplicity_X_sub_C_pow, Polynomial.rootMultiplicity_eq_zero hne, add_zero]

theorem rootMultiplicity_residualPoly_neg_one (L : ℕ) :
    (residualPoly L).rootMultiplicity (-1) = L := by
  have hne : ¬ (((Polynomial.X - Polynomial.C 1) ^ L : Polynomial ℂ)).IsRoot (-1) := by
    rw [Polynomial.IsRoot]
    simp only [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    refine pow_ne_zero _ ?_
    norm_num
  have hcomm : residualPoly L
      = (Polynomial.X - Polynomial.C (-1)) ^ L * (Polynomial.X - Polynomial.C 1) ^ L := by
    rw [residualPoly]; ring
  rw [hcomm, Polynomial.rootMultiplicity_mul (by rw [← hcomm]; exact residualPoly_ne_zero L),
    Polynomial.rootMultiplicity_X_sub_C_pow, Polynomial.rootMultiplicity_eq_zero hne, add_zero]

/-- The residual space `R_L` of `(5)`. -/
def residualSpace (L : ℕ) : Submodule ℂ (ℝ → ℂ) := solutionSpace (residualPoly L)

/-- **Equation (5), dimension.**  The rational residual space has dimension exactly `2 L = d_a`. -/
theorem finrank_residualSpace (L : ℕ) :
    Module.finrank ℂ (residualSpace L) = 2 * L := by
  rw [residualSpace, finrank_solutionSpace (residualPoly_ne_zero L), natDegree_residualPoly]

/-- **Equation (5), right modes.**  Every mode `x^j e^{x}` with `j < L` lies in the residual
space. -/
theorem charMode_one_mem_residualSpace {L j : ℕ} (hj : j < L) :
    charMode 1 j ∈ residualSpace L :=
  ⟨contDiff_charMode _ _,
    realConstCoeffOp_charMode (by rw [rootMultiplicity_residualPoly_one]; exact hj)⟩

/-- **Equation (5), left modes.**  Every mode `x^j e^{-x}` with `j < L` lies in the residual
space. -/
theorem charMode_neg_one_mem_residualSpace {L j : ℕ} (hj : j < L) :
    charMode (-1) j ∈ residualSpace L :=
  ⟨contDiff_charMode _ _,
    realConstCoeffOp_charMode (by rw [rootMultiplicity_residualPoly_neg_one]; exact hj)⟩

/-! ## The cross-boundary block -/

/-- **Equation (11).**  Against a right exterior point the Bessel tail expands into the `L` right
modes of the residual space. -/
theorem crossKernel_expansion_right (Q : Polynomial ℂ) {L : ℕ} (hQ : Q.natDegree < L) (y : ℝ) :
    (fun x : ℝ => Complex.exp (-((y : ℂ) - (x : ℂ))) * Q.eval ((y : ℂ) - (x : ℂ)))
      = ∑ j ∈ Finset.range L,
          (Complex.exp (-(y : ℂ))
            * (Q.comp (Polynomial.C (y : ℂ) - Polynomial.X)).coeff j) • charMode 1 j := by
  have hdeg : (Q.comp (Polynomial.C (y : ℂ) - Polynomial.X)).natDegree < L := by
    have hlin : (Polynomial.C (y : ℂ) - Polynomial.X).natDegree = 1 := by
      have hneg : Polynomial.C (y : ℂ) - Polynomial.X
          = -(Polynomial.X - Polynomial.C (y : ℂ)) := by ring
      rw [hneg, Polynomial.natDegree_neg, Polynomial.natDegree_X_sub_C]
    rw [Polynomial.natDegree_comp, hlin, mul_one]
    exact hQ
  funext x
  have hcomp : Q.eval ((y : ℂ) - (x : ℂ))
      = (Q.comp (Polynomial.C (y : ℂ) - Polynomial.X)).eval (x : ℂ) := by
    rw [Polynomial.eval_comp]
    simp
  have hexp : Complex.exp (-((y : ℂ) - (x : ℂ)))
      = Complex.exp (-(y : ℂ)) * Complex.exp ((x : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [hcomp, hexp, Polynomial.eval_eq_sum_range' hdeg]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, charMode, polyExp, polyExpC,
    Polynomial.eval_pow, Polynomial.eval_X, one_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **Equation (12).**  Against a left exterior point the Bessel tail expands into the `L` left
modes of the residual space. -/
theorem crossKernel_expansion_left (Q : Polynomial ℂ) {L : ℕ} (hQ : Q.natDegree < L) (y : ℝ) :
    (fun x : ℝ => Complex.exp (-((x : ℂ) - (y : ℂ))) * Q.eval ((x : ℂ) - (y : ℂ)))
      = ∑ j ∈ Finset.range L,
          (Complex.exp ((y : ℂ))
            * (Q.comp (Polynomial.X - Polynomial.C (y : ℂ))).coeff j) • charMode (-1) j := by
  have hdeg : (Q.comp (Polynomial.X - Polynomial.C (y : ℂ))).natDegree < L := by
    rw [Polynomial.natDegree_comp, Polynomial.natDegree_X_sub_C, mul_one]
    exact hQ
  funext x
  have hcomp : Q.eval ((x : ℂ) - (y : ℂ))
      = (Q.comp (Polynomial.X - Polynomial.C (y : ℂ))).eval (x : ℂ) := by
    rw [Polynomial.eval_comp]
    simp
  have hexp : Complex.exp (-((x : ℂ) - (y : ℂ)))
      = Complex.exp ((y : ℂ)) * Complex.exp (-(x : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [hcomp, hexp, Polynomial.eval_eq_sum_range' hdeg]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, charMode, polyExp, polyExpC,
    Polynomial.eval_pow, Polynomial.eval_X, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hneg : (-1 : ℂ) * (x : ℂ) = -(x : ℂ) := by ring
  rw [hneg]
  ring

/-! ## Stability of the Bessel tail under differentiation -/

/-- **Equation (10).**  Differentiating the Bessel tail keeps its shape. -/
theorem deriv_besselTail (Q : Polynomial ℂ) :
    deriv (polyExp Q (-1)) = polyExp (Polynomial.derivative Q - Q) (-1) := by
  rw [deriv_polyExp]
  congr 1
  rw [expShiftPoly]
  simp only [neg_smul, one_smul]
  ring

/-- **Equation (10), degree.**  The polynomial factor never gains degree. -/
theorem natDegree_besselTail_le (Q : Polynomial ℂ) :
    (Polynomial.derivative Q - Q).natDegree ≤ Q.natDegree :=
  le_trans (Polynomial.natDegree_sub_le _ _)
    (max_le (le_trans (Polynomial.natDegree_derivative_le Q) (Nat.sub_le _ _)) le_rfl)

/-! ## The finite Gram criterion -/

/-- The Gram matrix of the residual coordinate map. -/
def evansGramMatrix {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ := Aᴴ * A

theorem posSemidef_evansGramMatrix {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) :
    (evansGramMatrix A).PosSemidef :=
  Matrix.posSemidef_conjTranspose_mul_self A

/-- **Equation (15).**  The Gram quadratic form is the squared norm of the image. -/
theorem evansGram_quadratic {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (x : Fin n → ℂ) :
    star x ⬝ᵥ (evansGramMatrix A) *ᵥ x = star (A *ᵥ x) ⬝ᵥ (A *ᵥ x) := by
  rw [evansGramMatrix, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.star_mulVec]

theorem dotProduct_star_self_eq_zero_iff {n : ℕ} (y : Fin n → ℂ) :
    star y ⬝ᵥ y = 0 ↔ y = 0 := by
  constructor
  · intro h
    funext i
    have hsum : ∑ i, star (y i) * y i = 0 := h
    have hterm : ∀ i ∈ Finset.univ, (0 : ℝ) ≤ Complex.normSq (y i) := fun i _ =>
      Complex.normSq_nonneg _
    have hre : ∑ i, Complex.normSq (y i) = 0 := by
      have hcast : ((∑ i, Complex.normSq (y i) : ℝ) : ℂ) = ∑ i, star (y i) * y i := by
        push_cast
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Complex.normSq_eq_conj_mul_self]
        rfl
      have := hcast.trans hsum
      exact_mod_cast this
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp hre i (Finset.mem_univ i)
    exact Complex.normSq_eq_zero.mp hzero
  · intro h
    rw [h]
    simp

/-- **Equation (7), kernel step.**  The Gram matrix and the coordinate map have the same kernel. -/
theorem evansGramMatrix_mulVec_eq_zero_iff {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (x : Fin n → ℂ) :
    (evansGramMatrix A) *ᵥ x = 0 ↔ A *ᵥ x = 0 := by
  constructor
  · intro h
    refine (dotProduct_star_self_eq_zero_iff _).mp ?_
    rw [← evansGram_quadratic, h, dotProduct_zero]
  · intro h
    rw [evansGramMatrix, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero]

/-- **Equation (7).**  The residual map is injective exactly when the Gram determinant is
nonzero. -/
theorem det_evansGramMatrix_ne_zero_iff {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) :
    (evansGramMatrix A).det ≠ 0 ↔ ∀ x : Fin n → ℂ, A *ᵥ x = 0 → x = 0 := by
  constructor
  · intro hdet x hx
    by_contra hxne
    refine hdet ?_
    refine (Matrix.exists_mulVec_eq_zero_iff).mp ⟨x, hxne, ?_⟩
    exact (evansGramMatrix_mulVec_eq_zero_iff A x).mpr hx
  · intro hinj hdet
    obtain ⟨x, hxne, hx⟩ := (Matrix.exists_mulVec_eq_zero_iff).mpr hdet
    exact hxne (hinj x ((evansGramMatrix_mulVec_eq_zero_iff A x).mp hx))

/-- **Equation (7).**  Injectivity, positive definiteness and a positive determinant agree. -/
theorem posDef_evansGramMatrix_iff {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) :
    (evansGramMatrix A).PosDef ↔ ∀ x : Fin n → ℂ, A *ᵥ x = 0 → x = 0 := by
  rw [(posSemidef_evansGramMatrix A).posDef_iff_det_ne_zero, det_evansGramMatrix_ne_zero_iff]

/-- **Equation (7), determinant form.** -/
theorem det_evansGramMatrix_pos_iff {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) :
    0 < (evansGramMatrix A).det ↔ ∀ x : Fin n → ℂ, A *ᵥ x = 0 → x = 0 := by
  constructor
  · intro hpos
    exact (det_evansGramMatrix_ne_zero_iff A).mp (ne_of_gt hpos)
  · intro hinj
    exact ((posDef_evansGramMatrix_iff A).mpr hinj).det_pos

end GaloisForLFunctions.RHTower

end
