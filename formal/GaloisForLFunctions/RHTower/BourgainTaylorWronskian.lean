/-
# Full Wronskian for Bourgain's normalized Taylor curve

For the curve `(t,t²,φ₃(t),φ₄(t))`, the independent-point Wronskian in
Bourgain (1.1) is block lower triangular.  Its upper diagonal block has
determinant `2`; its lower diagonal block is exactly the separated jet
determinant from (2.11).

Combining this identity with the exact Taylor-phase bounds proves a uniform
`9/16` lower bound for Bourgain's actual normalized curve when
`0 < M/N₀ ≤ 1/2`.
-/
import GaloisForLFunctions.RHTower.BourgainTaylorScaling

namespace RHTower

noncomputable section

/-- First/second derivative block of `(t,t²)`. -/
def bourgainLinearQuadraticJetBlock
    (u : Fin 4 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 0; 2 * u 0, 2]

/-- First/second derivative block of the two higher phases. -/
def bourgainLowJetBlock
    (φ₃ φ₄ : ℝ → ℝ) (u : Fin 4 → ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  !![iteratedDeriv 1 φ₃ (u 0), iteratedDeriv 2 φ₃ (u 1);
     iteratedDeriv 1 φ₄ (u 0), iteratedDeriv 2 φ₄ (u 1)]

/-- Third/fourth derivative block of the two higher phases. -/
def bourgainHighJetBlock
    (φ₃ φ₄ : ℝ → ℝ) (u : Fin 4 → ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  !![iteratedDeriv 3 φ₃ (u 2), iteratedDeriv 4 φ₃ (u 3);
     iteratedDeriv 3 φ₄ (u 2), iteratedDeriv 4 φ₄ (u 3)]

/-- Bourgain's four-dimensional independent-point Wronskian in block order. -/
def bourgainFourCurveJetBlockMatrix
    (φ₃ φ₄ : ℝ → ℝ) (u : Fin 4 → ℝ) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ :=
  Matrix.fromBlocks
    (bourgainLinearQuadraticJetBlock u) 0
    (bourgainLowJetBlock φ₃ φ₄ u)
    (bourgainHighJetBlock φ₃ φ₄ u)

theorem det_bourgainLinearQuadraticJetBlock (u : Fin 4 → ℝ) :
    (bourgainLinearQuadraticJetBlock u).det = 2 := by
  simp [bourgainLinearQuadraticJetBlock, Matrix.det_fin_two]

theorem det_bourgainHighJetBlock
    (φ₃ φ₄ : ℝ → ℝ) (u : Fin 4 → ℝ) :
    (bourgainHighJetBlock φ₃ φ₄ u).det =
      bourgainSeparatedJetDet φ₃ φ₄ (u 2) (u 3) := by
  simp [bourgainHighJetBlock, bourgainSeparatedJetDet, Matrix.det_fin_two]
  ring

/-- Exact factorization of the Wronskian in (1.1) through the determinant
appearing in (2.11). -/
theorem det_bourgainFourCurveJetBlockMatrix
    (φ₃ φ₄ : ℝ → ℝ) (u : Fin 4 → ℝ) :
    (bourgainFourCurveJetBlockMatrix φ₃ φ₄ u).det =
      2 * bourgainSeparatedJetDet φ₃ φ₄ (u 2) (u 3) := by
  rw [bourgainFourCurveJetBlockMatrix,
    Matrix.det_fromBlocks_zero₁₂,
    det_bourgainLinearQuadraticJetBlock,
    det_bourgainHighJetBlock]

/-- Uniform quantitative certificate for Bourgain's full Wronskian
hypothesis (1.1) on the actual Taylor phases. -/
theorem det_bourgainFourCurveJetBlockMatrix_normalized_remainders_ge
    {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1 / 2)
    (u : Fin 4 → ℝ)
    (hu : ∀ i, u i ∈ Set.Icc (0 : ℝ) 1) :
    (9 / 16 : ℝ) ≤
      (bourgainFourCurveJetBlockMatrix
        (bourgainNormalizedCubicRemainder q)
        (bourgainNormalizedQuarticRemainder q) u).det := by
  rw [det_bourgainFourCurveJetBlockMatrix]
  have hdet :=
    bourgainSeparatedJetDet_normalized_remainders_ge
      hq0 hq1 (hu 2) (hu 3)
  nlinarith

end

end RHTower
