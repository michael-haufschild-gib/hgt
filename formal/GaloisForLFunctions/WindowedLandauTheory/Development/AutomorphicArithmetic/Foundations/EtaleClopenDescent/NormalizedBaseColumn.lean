import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveDiagonalColumns

/-! Exactness and contraction detection in the column after removing
all homogeneous normalization factors. -/

noncomputable section

open GlobalTheory.CechDR GlobalTheory.SchemeCohomology GlobalTheory.WH
open GlobalTheory.WH.WeightedChartSystem
open scoped GlobalTheory.CechDR GlobalTheory.SchemeCohomology TensorProduct

namespace GlobalTheory.PD

variable {k F E : Type} [Field k] [CharZero k] [Field F] [Field E]
  [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
  {d : ℕ} {x : Fin (d + 1) → F}

local instance {r : ℕ} : IsScalarTower k F (ExteriorDifferentials k E r) :=
  IsScalarTower.to₁₂₄ k F E (ExteriorDifferentials k E r)

/-- The base-coordinate Koszul complex in the regular chart lattice
after division by the normalization units. -/
def normalizedBaseColumn (h : IsPd k x) (q p : ℕ)
    (I J : Finset (Fin (d + 1))) (i j : Fin (d + 1)) :
    Cx k (Finset (DiagonalIndex d) → ExteriorDifferentials k E q ⊗[k] ExteriorDifferentials k E p) :=
  let T := diagonalChartSystem (E := E) h q p
  acx (fun _ => T.M I J)
    (fun l => T.act (T.normalizedWeight (fun _ => (1, 1)) T.homogeneousMinor i j l))

/-- In the normalized column, contractions detect top boundaries
at the subset of weights chosen by the right chart. -/
theorem IsFinCover.normalizedBaseColumn_exact_and_boundary (H : IsFinCover k E x) (q p : ℕ)
    {I J : Finset (Fin (d + 1))} {i j : Fin (d + 1)} (hi : i ∈ I) (hj : j ∈ J) :
    let C := normalizedBaseColumn (E := E) H.pd q p I J i j
    (∀ n : ℤ, n < (d : ℤ) → C.Z n ≤ C.B n) ∧
    (∀ a ∈ C.Z (d : ℤ), (∀ f : ExteriorDifferentials k E q →ₗ[F] F,
        tensorContraction f (a (selectedIndices (diagonalIndexEmbedding j))) = 0) →
      a ∈ C.B (d : ℤ)) := by
  let T := diagonalChartSystem (E := E) H.pd q p
  let G := diagonalChartSystem_good (E := E) H.pd q p
  let n : DiagonalIndex d → ℕ × ℕ := fun _ => (1, 1)
  let z := T.homogeneousMinor
  let C := normalizedBaseColumn (E := E) H.pd q p I J i j
  let D := T.columnComplex n z I J
  let e := T.scaleColumn n i j
  have hZ (m : ℤ) (a : Finset (DiagonalIndex d) → _) : e a ∈ D.Z m ↔ a ∈ C.Z m :=
    T.scaleColumn_mem_cycles_iff G n z hi hj m a
  have hB (m : ℤ) (a : Finset (DiagonalIndex d) → _) : e a ∈ D.B m ↔ a ∈ C.B m :=
    T.scaleColumn_mem_boundaries_iff G n z hi hj m a
  obtain ⟨hex, hdet⟩ := H.diagonalColumn_exact_and_boundary q p hi hj
  refine ⟨fun m hm a ha => (hB m a).mp (hex m hm ((hZ m a).mpr ha)), ?_⟩
  intro a ha hz
  apply (hB (d : ℤ) a).mp (hdet (e a) ((hZ (d : ℤ) a).mpr ha) ?_)
  intro f
  let L := selectedIndices (diagonalIndexEmbedding j)
  change tensorContraction f (tensorScalarAction (T.normalizationProduct n i j L : F ⊗[k] F) (a L)) = 0
  rw [tensorContraction_action, hz f, smul_zero]

end GlobalTheory.PD
