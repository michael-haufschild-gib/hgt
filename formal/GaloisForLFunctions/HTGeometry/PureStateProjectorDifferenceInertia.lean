import GaloisForLFunctions.HTGeometry.PureStateProjectorTangentInertia

/-!
# Exact rank-two inertia of a difference of pure-state rays

For two vectors `u,v`, subtract their positive rank-one observers and compress the result to the
ordered pair `(u,v)`.  The determinant is the negative square of the pair Gram determinant.
Thus projectively distinct rays produce an exact two-channel mixed-signature defect, independent
of their metric separation.  This is the discrete rank quantum needed when a trace norm can tend
to zero along nearly coincident rays.
-/

open scoped ComplexOrder InnerProductSpace Matrix

namespace HTGeometry

noncomputable section

open InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Difference of two positive rank-one rays. -/
def pureStateProjectorDifference (u v : E) : E →L[ℂ] E :=
  rankOne ℂ v v - rankOne ℂ u u

/-- Form compression of the two-ray difference to its generating pair. -/
def pureStateProjectorDifferenceCompression (u v : E) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun i j =>
    inner ℂ (![u, v] i) (pureStateProjectorDifference u v (![u, v] j))

/-- The two-ray difference determinant is the negative square of pair Gram energy. -/
theorem det_pureStateProjectorDifferenceCompression_eq_neg_sq_det_gram
    (u v : E) :
    (pureStateProjectorDifferenceCompression u v).det =
      -((Matrix.gram ℂ ![u, v]).det) ^ 2 := by
  rw [Matrix.det_fin_two, Matrix.det_fin_two]
  simp only [pureStateProjectorDifferenceCompression, pureStateProjectorDifference,
    Matrix.of_apply, Matrix.gram_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    _root_.sub_apply, rankOne_apply, inner_sub_right, inner_smul_right]
  ring

/-- Value-reflection form: projective Gram energy is squared and negated. -/
theorem det_pureStateProjectorDifferenceCompression_eq_neg_projectiveEnergy_sq
    (u v : E) :
    (pureStateProjectorDifferenceCompression u v).det =
      -((projectiveGramTangentEnergy (𝕜 := ℂ) u v : ℂ) ^ 2) := by
  rw [det_pureStateProjectorDifferenceCompression_eq_neg_sq_det_gram,
    det_gram_pair_eq_projectiveGramTangentEnergy]

/-- Every two-ray projector difference has a Hermitian pair compression. -/
theorem pureStateProjectorDifferenceCompression_isHermitian (u v : E) :
    (pureStateProjectorDifferenceCompression u v).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  fin_cases i <;> fin_cases j
  all_goals (simp [pureStateProjectorDifferenceCompression,
    pureStateProjectorDifference, inner_conj_symm] ; ring)

/-- Independent rays make the two-channel compression nonsingular. -/
theorem pureStateProjectorDifferenceCompression_det_ne_zero_of_linearIndependent
    {u v : E} (hli : LinearIndependent ℂ ![u, v]) :
    (pureStateProjectorDifferenceCompression u v).det ≠ 0 := by
  rw [det_pureStateProjectorDifferenceCompression_eq_neg_projectiveEnergy_sq]
  exact neg_ne_zero.mpr (pow_ne_zero 2
    (Complex.ofReal_ne_zero.mpr
      ((projectiveGramTangentEnergy_pos_iff_linearIndependent_pair u v).2 hli).ne'))

/-- A two-ray projector difference acts with two independent output directions whenever its
generating rays are independent. -/
theorem linearIndependent_pureStateProjectorDifference_images
    {u v : E} (hli : LinearIndependent ℂ ![u, v]) :
    LinearIndependent ℂ ![pureStateProjectorDifference u v u,
      pureStateProjectorDifference u v v] := by
  have hdet : (Matrix.gram ℂ ![u, v]).det ≠ 0 :=
    Matrix.det_gram_ne_zero_iff_linearIndependent.mpr hli
  rw [Matrix.det_fin_two] at hdet
  simp only [Matrix.gram_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at hdet
  have hcoef :
      (-inner ℂ u u) * inner ℂ v v ≠
        (inner ℂ v u) * (-inner ℂ u v) := by
    intro h
    apply hdet
    linear_combination -h
  rw [show pureStateProjectorDifference u v u =
      (-inner ℂ u u) • u + inner ℂ v u • v by
        simp [pureStateProjectorDifference]; module,
    show pureStateProjectorDifference u v v =
      (-inner ℂ u v) • u + inner ℂ v v • v by
        simp [pureStateProjectorDifference]; module,
    LinearIndependent.pair_add_smul_add_smul_iff]
  exact ⟨hli, hcoef⟩

/-- Independent rays force both signs in the compressed projector difference. -/
theorem pureStateProjectorDifferenceCompression_indefinite_of_linearIndependent
    {u v : E} (hli : LinearIndependent ℂ ![u, v]) :
    ¬ (pureStateProjectorDifferenceCompression u v).PosSemidef ∧
      ¬ (-pureStateProjectorDifferenceCompression u v).PosSemidef := by
  have henergy :=
    (projectiveGramTangentEnergy_pos_iff_linearIndependent_pair u v).2 hli
  constructor
  · intro hpsd
    have hnonneg := hpsd.det_nonneg
    rw [det_pureStateProjectorDifferenceCompression_eq_neg_projectiveEnergy_sq] at hnonneg
    have hre := (RCLike.nonneg_iff.mp hnonneg).1
    norm_num at hre
    rw [show ((((projectiveGramTangentEnergy (𝕜 := ℂ) u v : ℝ) : ℂ) ^ 2).re) =
        projectiveGramTangentEnergy (𝕜 := ℂ) u v ^ 2 by
      simp [pow_two, Complex.mul_re]] at hre
    nlinarith
  · intro hpsd
    have hnonneg := hpsd.det_nonneg
    rw [Matrix.det_neg] at hnonneg
    norm_num at hnonneg
    rw [det_pureStateProjectorDifferenceCompression_eq_neg_projectiveEnergy_sq] at hnonneg
    have hre := (RCLike.nonneg_iff.mp hnonneg).1
    norm_num at hre
    rw [show ((((projectiveGramTangentEnergy (𝕜 := ℂ) u v : ℝ) : ℂ) ^ 2).re) =
        projectiveGramTangentEnergy (𝕜 := ℂ) u v ^ 2 by
      simp [pow_two, Complex.mul_re]] at hre
    nlinarith

/-- Exact mixed-signature interface for a projectively distinct pair of pure rays. -/
theorem pureStateProjectorDifferenceCompression_exact_mixed_signature
    {u v : E} (hli : LinearIndependent ℂ ![u, v]) :
    let M := pureStateProjectorDifferenceCompression u v
    M.IsHermitian ∧ M.det ≠ 0 ∧
      ¬ M.PosSemidef ∧ ¬ (-M).PosSemidef := by
  exact ⟨pureStateProjectorDifferenceCompression_isHermitian u v,
    pureStateProjectorDifferenceCompression_det_ne_zero_of_linearIndependent hli,
    pureStateProjectorDifferenceCompression_indefinite_of_linearIndependent hli⟩

end

end HTGeometry
