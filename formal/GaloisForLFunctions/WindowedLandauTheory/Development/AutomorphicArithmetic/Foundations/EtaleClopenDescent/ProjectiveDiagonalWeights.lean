import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveDiagonalSystem
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveDiagonalRing

/-! On a pair of affine charts, the selected diagonal weights become
the coordinate differences after changing the left denominator. -/

noncomputable section

open GlobalTheory.WH.WeightedChartSystem
open scoped TensorProduct

namespace GlobalTheory.PD

variable {k F E : Type} [Field k] [Field F] [Field E] [Algebra k F]
  [Algebra k E] [Algebra F E] [IsScalarTower k F E]
  {d : ℕ} {x : Fin (d + 1) → F} (h : IsPd k x) (p q : ℕ)

/-- Changing the left denominator multiplies the common-chart
coordinate differences by its new coordinate ratio. -/
theorem diagonalMinor_normalized_of_common (i j : Fin (d + 1))
    {I J : Finset (Fin (d + 1))} (hi : j ∈ I) (hj : j ∈ J) (l : Fin d) :
    (diagonalChartSystem (E := E) h p q).normalizedWeight (fun _ => (1, 1))
        (diagonalMinor (E := E) h p q) i j (diagonalIndexEmbedding j l) =
      ((x j / x i) ⊗ₜ[k] (1 : F)) * (h.chartDiagonalGenerators hi hj l : F ⊗[k] F) := by
  change (diagonalChartSystem (E := E) h p q).normalizedWeight (fun _ => (1, 1))
    (diagonalMinor (E := E) h p q) i j (toLex (j.succAbove l, j)) = _
  rw [diagonalMinor_normalized, h.chartDiagonalGenerators_coe hi hj,
    div_self (h.ne j), mul_sub, Algebra.TensorProduct.tmul_mul_tmul,
    Algebra.TensorProduct.tmul_mul_tmul]
  have he : x (j.succAbove l) / x i = (x j / x i) * chartCoordinates x j l := by
    unfold chartCoordinates
    field_simp [h.ne i, h.ne j]
  simp only [one_mul, mul_one, he]
  rfl

/-- For distinct denominators, one of the selected equations makes
the left localization denominator invertible modulo the weight ideal. -/
theorem exists_diagonalMinor_normalized_one_sub (i j : Fin (d + 1)) (hij : i ≠ j) :
    ∃ l : Fin d, (diagonalChartSystem (E := E) h p q).normalizedWeight (fun _ => (1, 1))
      (diagonalMinor (E := E) h p q) i j (diagonalIndexEmbedding j l) =
      1 - ((x j / x i) ⊗ₜ[k] (1 : F)) * ((1 : F) ⊗ₜ[k] (x i / x j)) := by
  obtain ⟨l, hl⟩ := Fin.exists_succAbove_eq hij
  refine ⟨l, ?_⟩
  change (diagonalChartSystem (E := E) h p q).normalizedWeight (fun _ => (1, 1))
    (diagonalMinor (E := E) h p q) i j (toLex (j.succAbove l, j)) = _
  rw [hl, diagonalMinor_normalized, div_self (h.ne i), div_self (h.ne j),
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, ← Algebra.TensorProduct.one_def]

end GlobalTheory.PD
