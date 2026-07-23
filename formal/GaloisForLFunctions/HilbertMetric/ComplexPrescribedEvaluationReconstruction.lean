import GaloisForLFunctions.HilbertMetric.PrescribedEvaluationReconstruction

/-!
# Exact complex reconstruction on a prescribed evaluation packet

The real prescribed-packet criterion has a complex Hermitian counterpart.  For a fixed square
packet of complex samples, exact dual coefficient recovery is equivalent to nonsingularity of the
literal evaluation matrix.  The same condition is equivalent to strict positivity of its
Hermitian evaluation Gram.
-/

namespace GaloisForLFunctions.HilbertMetric

noncomputable section

open scoped BigOperators ComplexOrder

variable {κ X : Type*} [Fintype κ] [DecidableEq κ]

/-- Unit-spaced complex sample packet based at a real point. -/
def complexArithmeticNodes {n : ℕ} (x : ℝ) : Fin n → ℂ :=
  fun row => (x : ℂ) + (row : ℕ)

/-- A unit-spaced complex sample packet has no repeated nodes. -/
theorem complexArithmeticNodes_injective {n : ℕ} (x : ℝ) :
    Function.Injective (complexArithmeticNodes (n := n) x) := by
  intro i j hij
  apply Fin.ext
  have hcast : ((i : ℕ) : ℂ) = ((j : ℕ) : ℂ) := by
    exact add_left_cancel hij
  exact_mod_cast hcast

/-- Literal complex evaluation matrix of a finite feature family on a prescribed square packet. -/
def complexEvaluationMatrix (u : κ → X → ℂ) (points : κ → X) :
    Matrix κ κ ℂ :=
  fun row col => u col (points row)

/-- Evaluation column of one complex feature on a prescribed square packet. -/
def complexEvaluationColumn (u : κ → X → ℂ) (points : κ → X) (j : κ) :
    EuclideanSpace ℂ κ :=
  WithLp.toLp 2 fun row => u j (points row)

/-- Hermitian Gram of the prescribed complex evaluation columns. -/
def complexEvaluationGram (u : κ → X → ℂ) (points : κ → X) :
    Matrix κ κ ℂ :=
  Matrix.gram ℂ (complexEvaluationColumn u points)

/-- A prescribed complex packet has dual weights that isolate every feature and recover every
complex coefficient vector from its literal sampled values. -/
def PrescribedComplexEvaluationDualReconstruction
    (u : κ → X → ℂ) (points : κ → X) : Prop :=
  ∃ dual : κ → κ → ℂ,
    (∀ q r, ∑ i, dual q i * u r (points i) = if q = r then 1 else 0) ∧
    ∀ (a : κ → ℂ) q,
      ∑ i, dual q i * (∑ r, a r * u r (points i)) = a q

omit [DecidableEq κ] in
/-- The prescribed complex Gram is the adjoint-square of the literal evaluation matrix. -/
theorem complexEvaluationGram_eq_conjTranspose_mul
    (u : κ → X → ℂ) (points : κ → X) :
    complexEvaluationGram u points =
      (complexEvaluationMatrix u points).conjTranspose *
        complexEvaluationMatrix u points := by
  rw [complexEvaluationGram,
    Matrix.gram_eq_conjTranspose_mul (EuclideanSpace.basisFun κ ℂ)]
  rfl

/-- Exact prescribed complex Hilbert-volume identity. -/
theorem complexEvaluationGram_det_eq_normSq
    (u : κ → X → ℂ) (points : κ → X) :
    (complexEvaluationGram u points).det =
      (Complex.normSq (complexEvaluationMatrix u points).det : ℂ) := by
  rw [complexEvaluationGram_eq_conjTranspose_mul,
    Matrix.det_mul, Matrix.det_conjTranspose,
    Complex.normSq_eq_conj_mul_self]
  rfl

/-- Exact dual recovery on a fixed complex packet is equivalent to nonsingularity of its literal
evaluation matrix. -/
theorem prescribedComplexEvaluationDualReconstruction_iff_det_ne_zero
    (u : κ → X → ℂ) (points : κ → X) :
    PrescribedComplexEvaluationDualReconstruction u points ↔
      (complexEvaluationMatrix u points).det ≠ 0 := by
  constructor
  · rintro ⟨dual, hdelta, _hrecovery⟩
    let D : Matrix κ κ ℂ := fun q i => dual q i
    have hleft : D * complexEvaluationMatrix u points = 1 := by
      ext q r
      simpa [D, Matrix.mul_apply, complexEvaluationMatrix] using hdelta q r
    exact Matrix.det_ne_zero_of_left_inverse hleft
  · intro hdet
    let P : Matrix κ κ ℂ := complexEvaluationMatrix u points
    let dual : κ → κ → ℂ := fun q i => P⁻¹ q i
    have hunit : IsUnit P.det := isUnit_iff_ne_zero.mpr (by simpa [P] using hdet)
    have hdelta : ∀ q r, ∑ i, dual q i * u r (points i) =
        if q = r then 1 else 0 := by
      intro q r
      have hentry := congrArg (fun M : Matrix κ κ ℂ => M q r)
        (P.nonsing_inv_mul hunit)
      simpa [dual, P, Matrix.mul_apply, complexEvaluationMatrix] using hentry
    refine ⟨dual, hdelta, ?_⟩
    intro a q
    calc
      ∑ i, dual q i * (∑ r, a r * u r (points i)) =
          ∑ i, ∑ r, dual q i * (a r * u r (points i)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
      _ = ∑ r, ∑ i, dual q i * (a r * u r (points i)) :=
        Finset.sum_comm
      _ = ∑ r, a r * (∑ i, dual q i * u r (points i)) := by
        apply Finset.sum_congr rfl
        intro r _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = ∑ r, a r * (if q = r then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro r _
        rw [hdelta q r]
      _ = a q := by simp

omit [DecidableEq κ] in
/-- Linear independence of prescribed complex evaluation columns is the same whether the columns
are viewed in the Euclidean Hilbert space or as columns of the literal evaluation matrix. -/
theorem linearIndependent_complexEvaluationColumn_iff
    (u : κ → X → ℂ) (points : κ → X) :
    LinearIndependent ℂ (complexEvaluationColumn u points) ↔
      LinearIndependent ℂ (complexEvaluationMatrix u points).col := by
  constructor
  · intro hcolumns
    rw [Fintype.linearIndependent_iff] at hcolumns ⊢
    intro c hc
    apply hcolumns c
    ext row
    have hrow := congrArg (fun v : κ → ℂ => v row) hc
    simpa [complexEvaluationColumn, complexEvaluationMatrix,
      Matrix.col_apply, Finset.sum_apply, Pi.smul_apply] using hrow
  · intro hmatrix
    rw [Fintype.linearIndependent_iff] at hmatrix ⊢
    intro c hc
    apply hmatrix c
    funext row
    have hrow := congrArg (fun v : EuclideanSpace ℂ κ => v row) hc
    simpa [complexEvaluationColumn, complexEvaluationMatrix,
      Matrix.col_apply, Finset.sum_apply, Pi.smul_apply] using hrow

/-- Exact prescribed complex reconstruction is equivalent to strict positivity of the Hermitian
evaluation Gram on the same fixed packet. -/
theorem prescribedComplexEvaluationDualReconstruction_iff_gram_posDef
    (u : κ → X → ℂ) (points : κ → X) :
    PrescribedComplexEvaluationDualReconstruction u points ↔
      (complexEvaluationGram u points).PosDef := by
  rw [prescribedComplexEvaluationDualReconstruction_iff_det_ne_zero]
  constructor
  · intro hdet
    have hcols : LinearIndependent ℂ (complexEvaluationMatrix u points).col :=
      Matrix.linearIndependent_cols_iff_isUnit.mpr
        ((Matrix.isUnit_iff_isUnit_det _).mpr
          (isUnit_iff_ne_zero.mpr hdet))
    exact Matrix.posDef_gram_of_linearIndependent
      ((linearIndependent_complexEvaluationColumn_iff u points).mpr hcols)
  · intro hgram
    have hcolumns : LinearIndependent ℂ (complexEvaluationColumn u points) :=
      Matrix.posDef_gram_iff_linearIndependent.mp hgram
    have hcols : LinearIndependent ℂ (complexEvaluationMatrix u points).col :=
      (linearIndependent_complexEvaluationColumn_iff u points).mp hcolumns
    exact ((Matrix.isUnit_iff_isUnit_det _).mp
      (Matrix.linearIndependent_cols_iff_isUnit.mp hcols)).ne_zero

end

end GaloisForLFunctions.HilbertMetric
