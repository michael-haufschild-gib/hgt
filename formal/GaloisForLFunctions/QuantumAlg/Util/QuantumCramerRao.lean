import GaloisForLFunctions.QuantumAlg.Util.QuantumFisher
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.MeanInequalities

/-!
# Finite-dimensional SLD Cramer--Rao geometry

This module adds the operational layer used in arXiv:2608.25870 to the corpus QFIM:
`C = Tr(Q⁻¹)` and `s = det(Q⁻¹)`.  A positive QFIM is bundled so all public theorems
are closed: identifiability is data, not an extra theorem premise.
-/

namespace QuantumAlg

open Matrix

noncomputable section

/-- An identifiable `(m+1)`-parameter Fisher model: its QFIM is positive definite. -/
structure PositiveQFIM (m : ℕ) where
  matrix : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ
  posDef : matrix.PosDef

/-- SLD Cramer--Rao total error `Tr(Q⁻¹)`. -/
def PositiveQFIM.sldCramerRao {m : ℕ} (Q : PositiveQFIM m) : ℝ :=
  Q.matrix⁻¹.trace

/-- Determinant sloppiness `det(Q⁻¹)`, the error-volume invariant. -/
def PositiveQFIM.sloppiness {m : ℕ} (Q : PositiveQFIM m) : ℝ :=
  Q.matrix⁻¹.det

theorem PositiveQFIM.sldCramerRao_pos {m : ℕ} (Q : PositiveQFIM m) :
    0 < Q.sldCramerRao := by
  exact Q.posDef.inv.trace_pos

theorem PositiveQFIM.sloppiness_pos {m : ℕ} (Q : PositiveQFIM m) :
    0 < Q.sloppiness := by
  exact Q.posDef.inv.det_pos

/-- Paper's sloppiness law, with dimension forced nonzero by indexing parameters by
`Fin (m+1)`: geometric mean error-volume is at most mean marginal SLD error. -/
theorem PositiveQFIM.sloppiness_rpow_inv_dimension_le_mean_sldCramerRao
    {m : ℕ} (Q : PositiveQFIM m) :
    Q.sloppiness ^ (((m + 1 : ℕ) : ℝ)⁻¹) ≤
      Q.sldCramerRao / (m + 1 : ℕ) := by
  let B : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ := Q.matrix⁻¹
  have hB : B.PosDef := Q.posDef.inv
  have hAM := Real.geom_mean_le_arith_mean
    (Finset.univ : Finset (Fin (m + 1)))
    (fun _ => (1 : ℝ)) (fun i => hB.1.eigenvalues i)
    (fun _ _ => by norm_num)
    (by positivity)
    (fun i _ => (hB.eigenvalues_pos i).le)
  rw [show Q.sloppiness = B.det by rfl,
    show Q.sldCramerRao = B.trace by rfl,
    hB.1.det_eq_prod_eigenvalues, hB.1.trace_eq_sum_eigenvalues]
  simpa using hAM

/-- Positive scalar Fisher information, used for one-parameter corpus applications. -/
structure PositiveScalarQFI where
  value : ℝ
  positive : 0 < value

/-- One-parameter SLD Cramer--Rao error. -/
def PositiveScalarQFI.sldCramerRao (Q : PositiveScalarQFI) : ℝ := Q.value⁻¹

theorem PositiveScalarQFI.sldCramerRao_pos (Q : PositiveScalarQFI) :
    0 < Q.sldCramerRao := inv_pos.mpr Q.positive

/-- Reparameterize a positive scalar QFI by a nonzero clock rate. -/
def PositiveScalarQFI.clockRateScale (Q : PositiveScalarQFI) (rate : ℝˣ) :
    PositiveScalarQFI where
  value := (rate : ℝ) ^ 2 * Q.value
  positive := mul_pos (sq_pos_of_ne_zero (Units.ne_zero rate)) Q.positive

/-- SLD error transforms contravariantly to the quadratic QFI clock-rate law. -/
theorem PositiveScalarQFI.sldCramerRao_clockRateScale
    (Q : PositiveScalarQFI) (rate : ℝˣ) :
    (Q.clockRateScale rate).sldCramerRao =
      ((rate : ℝ) ^ 2)⁻¹ * Q.sldCramerRao := by
  unfold PositiveScalarQFI.sldCramerRao PositiveScalarQFI.clockRateScale
  rw [_root_.mul_inv_rev]
  exact mul_comm _ _

/-- Extended scalar SLD error.  Zero/nonpositive information maps to infinite error,
so PSD but singular one-parameter models remain meaningful. -/
def extendedScalarSLDCramerRao (q : ℝ) : ENNReal :=
  (ENNReal.ofReal q)⁻¹

theorem extendedScalarSLDCramerRao_congr {q q' : ℝ} (h : q = q') :
    extendedScalarSLDCramerRao q = extendedScalarSLDCramerRao q' := by
  rw [h]

theorem extendedScalarSLDCramerRao_zero :
    extendedScalarSLDCramerRao 0 = ⊤ := by
  simp [extendedScalarSLDCramerRao]

/-- Extended SLD error is infinite exactly for nonpositive scalar information. -/
theorem extendedScalarSLDCramerRao_eq_top_iff (q : ℝ) :
    extendedScalarSLDCramerRao q = ⊤ ↔ q ≤ 0 := by
  simp [extendedScalarSLDCramerRao]

/-- For a positive-semidefinite scalar model, infinite SLD error is exactly zero QFI. -/
theorem extendedScalarSLDCramerRao_eq_top_iff_eq_zero
    (q : ℝ) (hq : 0 ≤ q) :
    extendedScalarSLDCramerRao q = ⊤ ↔ q = 0 := by
  rw [extendedScalarSLDCramerRao_eq_top_iff]
  exact ⟨fun h => le_antisymm h hq, fun h => h.le⟩

/-- A pure-state generator model with identifiability bundled into its data. -/
structure IdentifiablePureStateQFIM (n : Type*) [Fintype n] (m : ℕ) where
  state : n → ℂ
  generators : Fin (m + 1) → Matrix n n ℂ
  normalized : star state ⬝ᵥ state = 1
  hermitian : ∀ i, (generators i)ᴴ = generators i
  identifiable : (qfim state generators).PosDef

def IdentifiablePureStateQFIM.toPositiveQFIM
    {n : Type*} [Fintype n] {m : ℕ} (model : IdentifiablePureStateQFIM n m) :
    PositiveQFIM m where
  matrix := qfim model.state model.generators
  posDef := model.identifiable

theorem IdentifiablePureStateQFIM.qfim_posSemidef
    {n : Type*} [Fintype n] {m : ℕ} (model : IdentifiablePureStateQFIM n m) :
    (qfim model.state model.generators).PosSemidef :=
  QuantumAlg.qfim_posSemidef model.normalized model.hermitian

/-- Every identifiable corpus QFIM inherits the paper's error-volume bound. -/
theorem IdentifiablePureStateQFIM.sloppiness_le_mean_error
    {n : Type*} [Fintype n] {m : ℕ} (model : IdentifiablePureStateQFIM n m) :
    model.toPositiveQFIM.sloppiness ^ (((m + 1 : ℕ) : ℝ)⁻¹) ≤
      model.toPositiveQFIM.sldCramerRao / (m + 1 : ℕ) :=
  model.toPositiveQFIM.sloppiness_rpow_inv_dimension_le_mean_sldCramerRao

end

end QuantumAlg
