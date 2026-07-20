import GaloisForLFunctions.HTGeometry.QuantumGeometricTensorGram

/-!
# Exact rank-two inertia of a pure-state projector tangent

For vectors `u,v` in a complex inner-product space, the first variation of the rank-one
projector in direction `v` is

```text
T(u,v) = |v><u| + |u><v|.
```

Its form matrix on the ordered pair `(u,v)` has determinant equal to the negative square of the
ordinary Gram determinant.  Equivalently, it is the negative square of the projective
Gram/Fisher tangent energy.  Linear independence therefore gives an exact mixed-signature
certificate: the compression is Hermitian and nonsingular, and neither it nor its negative is
positive semidefinite.

This is a value-reflection law.  The nonnegative Gram value is reflected across zero and squared
to become the projector-tangent determinant.  It packages the standard pure-state tangent
calculation into the `Matrix.PosSemidef` and `LinearIndependent` interfaces used downstream.
-/

open scoped ComplexOrder InnerProductSpace Matrix

namespace HTGeometry

noncomputable section

open InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- First variation of a rank-one projector along the pair `(u,v)`. -/
def pureStateProjectorTangent (u v : E) : E →L[ℂ] E :=
  rankOne ℂ v u + rankOne ℂ u v

/-- Form matrix of the projector tangent on the ordered pair `(u,v)`. -/
def pureStateProjectorTangentCompression (u v : E) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun i j =>
    inner ℂ (![u, v] i) (pureStateProjectorTangent u v (![u, v] j))

/-- The projector-tangent determinant is the negative square of the pair Gram determinant. -/
theorem det_pureStateProjectorTangentCompression_eq_neg_sq_det_gram
    (u v : E) :
    (pureStateProjectorTangentCompression u v).det =
      -((Matrix.gram ℂ ![u, v]).det) ^ 2 := by
  rw [Matrix.det_fin_two, Matrix.det_fin_two]
  simp only [pureStateProjectorTangentCompression, pureStateProjectorTangent,
    Matrix.of_apply, Matrix.gram_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    ContinuousLinearMap.add_apply, rankOne_apply, inner_add_right,
    inner_smul_right]
  ring

/-- Value-reflection form of the determinant law: projective energy is squared and negated. -/
theorem det_pureStateProjectorTangentCompression_eq_neg_projectiveEnergy_sq
    (u v : E) :
    (pureStateProjectorTangentCompression u v).det =
      -((projectiveGramTangentEnergy (𝕜 := ℂ) u v : ℂ) ^ 2) := by
  rw [det_pureStateProjectorTangentCompression_eq_neg_sq_det_gram,
    det_gram_pair_eq_projectiveGramTangentEnergy]

/-- The form matrix of every pure-state projector tangent is Hermitian. -/
theorem pureStateProjectorTangentCompression_isHermitian (u v : E) :
    (pureStateProjectorTangentCompression u v).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  fin_cases i <;> fin_cases j
  all_goals (simp [pureStateProjectorTangentCompression,
    pureStateProjectorTangent, inner_conj_symm] ; ring)

/-- Positive projective Gram energy is exactly complex independence of the two channels. -/
theorem projectiveGramTangentEnergy_pos_iff_linearIndependent_pair
    (u v : E) :
    0 < projectiveGramTangentEnergy (𝕜 := ℂ) u v ↔
      LinearIndependent ℂ ![u, v] := by
  exact (quantumMetricArea_strict_iff_projectiveGram_pos u v).symm.trans
    (quantumMetricArea_strict_iff_linearIndependent_pair u v)

private theorem not_posSemidef_of_det_eq_neg_sq
    {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} {e : ℝ}
    (he : 0 < e) (hdet : M.det = -((e : ℂ) ^ 2)) :
    ¬ M.PosSemidef := by
  intro hpsd
  have hnonneg := hpsd.det_nonneg
  rw [hdet] at hnonneg
  have hre := (RCLike.nonneg_iff.mp hnonneg).1
  norm_num at hre
  rw [show (((e : ℂ) ^ 2).re) = e ^ 2 by
    simp [pow_two, Complex.mul_re]] at hre
  nlinarith

/-- Independent channels force both signs: neither compression nor its negative is PSD. -/
theorem pureStateProjectorTangentCompression_indefinite_of_linearIndependent
    {u v : E} (hli : LinearIndependent ℂ ![u, v]) :
    ¬ (pureStateProjectorTangentCompression u v).PosSemidef ∧
      ¬ (-pureStateProjectorTangentCompression u v).PosSemidef := by
  have henergy :=
    (projectiveGramTangentEnergy_pos_iff_linearIndependent_pair u v).2 hli
  refine ⟨not_posSemidef_of_det_eq_neg_sq henergy
    (det_pureStateProjectorTangentCompression_eq_neg_projectiveEnergy_sq u v), ?_⟩
  apply not_posSemidef_of_det_eq_neg_sq henergy
  rw [Matrix.det_neg]
  norm_num
  exact det_pureStateProjectorTangentCompression_eq_neg_projectiveEnergy_sq u v

/-- Independent channels also make the projector-tangent compression nonsingular. -/
theorem pureStateProjectorTangentCompression_det_ne_zero_of_linearIndependent
    {u v : E} (hli : LinearIndependent ℂ ![u, v]) :
    (pureStateProjectorTangentCompression u v).det ≠ 0 := by
  rw [det_pureStateProjectorTangentCompression_eq_neg_projectiveEnergy_sq]
  exact neg_ne_zero.mpr (pow_ne_zero 2
    (Complex.ofReal_ne_zero.mpr
      ((projectiveGramTangentEnergy_pos_iff_linearIndependent_pair u v).2 hli).ne'))

/-- Exact mixed-signature interface for the rank-two pure-state tangent compression. -/
theorem pureStateProjectorTangentCompression_exact_mixed_signature
    {u v : E} (hli : LinearIndependent ℂ ![u, v]) :
    let M := pureStateProjectorTangentCompression u v
    M.IsHermitian ∧ M.det ≠ 0 ∧
      ¬ M.PosSemidef ∧ ¬ (-M).PosSemidef := by
  exact ⟨pureStateProjectorTangentCompression_isHermitian u v,
    pureStateProjectorTangentCompression_det_ne_zero_of_linearIndependent hli,
    pureStateProjectorTangentCompression_indefinite_of_linearIndependent hli⟩

end

end HTGeometry
