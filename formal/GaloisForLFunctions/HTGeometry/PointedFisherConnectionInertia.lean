import GaloisForLFunctions.HTGeometry.PureStateProjectorTangentInertia
import GaloisForLFunctions.HTGeometry.RankTwoFisherCutoffWard

/-!
# Mixed signature of the pointed Fisher connection

The existing pointed Fisher connection is the positive normalization `2⁻¹ᐟ²` of the pure-state
projector tangent.  This module joins its Hilbert--Schmidt/Ward laws to the exact projector-tangent
determinant law.  On an independent state--tangent pair, its form matrix is Hermitian and
nonsingular with both signs, while its determinant is exactly minus one half of the squared
projective Gram/Fisher energy.

Consequently, positive Hilbert--Schmidt energy of the Fisher connection must not be confused with
positive-operator order.  This is a parent-theory bridge and a reusable negative-control
interface, not a new quantum-geometric claim.
-/

open scoped ComplexOrder InnerProductSpace Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The pointed Fisher connection is the normalized pure-state projector tangent. -/
theorem pointedFisherConnection_eq_invSqrtTwo_smul_pureStateProjectorTangent
    (u v : E) :
    pointedFisherConnection u v =
      ((Real.sqrt 2)⁻¹ : ℂ) • _root_.HTGeometry.pureStateProjectorTangent u v := by
  rfl

/-- Form matrix of the pointed Fisher connection on its defining pair. -/
def pointedFisherConnectionCompression (u v : E) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun i j =>
    inner ℂ (![u, v] i) (pointedFisherConnection u v (![u, v] j))

private theorem pointedFisherConnectionCompression_eq_complex_smul
    (u v : E) :
    pointedFisherConnectionCompression u v =
      ((Real.sqrt 2)⁻¹ : ℂ) •
        _root_.HTGeometry.pureStateProjectorTangentCompression u v := by
  ext i j
  simp [pointedFisherConnectionCompression, pointedFisherConnection,
    _root_.HTGeometry.pureStateProjectorTangentCompression,
    _root_.HTGeometry.pureStateProjectorTangent]
  ring

/-- Compression-level bridge in the real positive-scalar interface used by matrix order. -/
theorem pointedFisherConnectionCompression_eq_invSqrtTwo_smul
    (u v : E) :
    pointedFisherConnectionCompression u v =
      (Real.sqrt 2)⁻¹ •
        _root_.HTGeometry.pureStateProjectorTangentCompression u v := by
  rw [pointedFisherConnectionCompression_eq_complex_smul]
  ext i j
  simp [smul_eq_mul]

private theorem inv_sqrt_two_sq :
    (((Real.sqrt 2)⁻¹ : ℂ) ^ 2) = (1 / 2 : ℂ) := by
  rw [inv_pow, ← Complex.ofReal_pow,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

/-- The normalized Fisher determinant is minus one half of squared projective energy. -/
theorem det_pointedFisherConnectionCompression_eq_neg_half_projectiveEnergy_sq
    (u v : E) :
    (pointedFisherConnectionCompression u v).det =
      -(1 / 2 : ℂ) *
        (_root_.HTGeometry.projectiveGramTangentEnergy (𝕜 := ℂ) u v : ℂ) ^ 2 := by
  rw [pointedFisherConnectionCompression_eq_complex_smul, Matrix.det_smul,
    Fintype.card_fin,
    _root_.HTGeometry.det_pureStateProjectorTangentCompression_eq_neg_projectiveEnergy_sq,
    inv_sqrt_two_sq]
  ring

private theorem posSemidef_unscale_inv_sqrt_two
    {M : Matrix (Fin 2) (Fin 2) ℂ}
    (h : (((Real.sqrt 2)⁻¹ : ℝ) • M).PosSemidef) :
    M.PosSemidef := by
  have hscaled := h.smul (Real.sqrt_nonneg 2)
  simpa [smul_smul,
    Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2)] using hscaled

/-- Exact mixed-signature interface for an independent pointed state--tangent pair. -/
theorem pointedFisherConnectionCompression_exact_mixed_signature
    {u v : E} (hli : LinearIndependent ℂ ![u, v]) :
    let M := pointedFisherConnectionCompression u v
    M.IsHermitian ∧ M.det ≠ 0 ∧
      ¬ M.PosSemidef ∧ ¬ (-M).PosSemidef := by
  let G := _root_.HTGeometry.pureStateProjectorTangentCompression u v
  have hG :=
    _root_.HTGeometry.pureStateProjectorTangentCompression_exact_mixed_signature hli
  have heq : pointedFisherConnectionCompression u v = (Real.sqrt 2)⁻¹ • G :=
    pointedFisherConnectionCompression_eq_invSqrtTwo_smul u v
  have hrpos : 0 < (Real.sqrt 2)⁻¹ :=
    inv_pos.mpr (Real.sqrt_pos.2 (by norm_num))
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [heq]
    exact IsSelfAdjoint.smul (IsSelfAdjoint.of_nonneg hrpos.le) hG.1
  · rw [det_pointedFisherConnectionCompression_eq_neg_half_projectiveEnergy_sq]
    exact mul_ne_zero (neg_ne_zero.mpr (by norm_num))
      (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr
        ((_root_.HTGeometry.projectiveGramTangentEnergy_pos_iff_linearIndependent_pair
          u v).2 hli).ne'))
  · rw [heq]
    intro hpsd
    exact hG.2.2.1 (posSemidef_unscale_inv_sqrt_two hpsd)
  · rw [heq]
    intro hpsd
    have hscaled : (((Real.sqrt 2)⁻¹ : ℝ) • (-G)).PosSemidef := by
      simpa only [smul_neg] using hpsd
    exact hG.2.2.2 (posSemidef_unscale_inv_sqrt_two hscaled)

end

end GaloisForLFunctions.HTGeometry
