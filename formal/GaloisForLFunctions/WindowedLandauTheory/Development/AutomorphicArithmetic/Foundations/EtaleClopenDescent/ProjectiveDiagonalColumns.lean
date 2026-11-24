import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveDiagonalKoszul
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.WeightedChartSelectedColumn
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.KoszulLatticeIdentification

/-! The homogeneous diagonal column is exact below the relative
dimension. In top degree its boundaries are detected by contraction
of the component selected by the right coordinate. -/

noncomputable section

open GlobalTheory.CechDR GlobalTheory.SchemeCohomology GlobalTheory.WH
open GlobalTheory.WH.WeightedChartSystem
open scoped GlobalTheory.CechDR GlobalTheory.SchemeCohomology TensorProduct

namespace GlobalTheory.PD

variable {k F E : Type} [Field k] [CharZero k] [Field F] [Field E]
  [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
  {d : ℕ} {x : Fin (d + 1) → F}
  {I J : Finset (Fin (d + 1))} {i j : Fin (d + 1)}
  (h : IsFinCover k E x) (p q : ℕ) (hi : i ∈ I) (hj : j ∈ J)

local instance {r : ℕ} : IsScalarTower k F (ExteriorDifferentials k E r) :=
  IsScalarTower.to₁₂₄ k F E (ExteriorDifferentials k E r)

local notation "V₀" => ExteriorDifferentials k E p ⊗[k] ExteriorDifferentials k E q
local notation "R₀" => tensorChartRing (rA k x I) (rA k x J)
local notation "n₀" => (fun _ : DiagonalIndex d => ((1, 1) : ℕ × ℕ))
local notation "e₀" => diagonalIndexEmbedding j

include hi hj in
private theorem normalizedSelected_exact (m : ℤ) (hm : m < (d : ℤ)) :
    let T := diagonalChartSystem (E := E) h.pd p q
    let C : Cx k (Finset (Fin d) → V₀) :=
      acx (fun _ => T.M I J) (fun l => T.act (T.normalizedWeight n₀ T.homogeneousMinor i j (e₀ l)))
    C.Z m ≤ C.B m := by
  let T := diagonalChartSystem (E := E) h.pd p q
  letI chartAction : Module R₀ V₀ := tensorChartModule (rA k x I) (rA k x J)
  letI chartTower : IsScalarTower k R₀ V₀ := T.chartScalarTower
  let P : Submodule R₀ V₀ := projectiveTensorLattice (k := k) (E := E) (x := x) I J p q
  let r := normalizedDiagonalWeights (E := E) h.pd p q hi hj
  let w (l : Fin d) : Module.End k V₀ :=
    T.act (T.normalizedWeight n₀ T.homogeneousMinor i j (e₀ l))
  have hP : P.restrictScalars k = T.M I J := Submodule.ext fun _ => Iff.rfl
  have hw : (fun l => Algebra.lsmul k k V₀ (r l)) = w :=
    funext fun _ => LinearMap.ext fun _ => rfl
  exact @acx_exact_of_lattice_identification k R₀ V₀ (Fin d)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    chartAction chartTower P r (T.M I J) w hP hw m
    ((h.normalizedDiagonal_lattice p q hi hj).1 m hm)

include hi hj in
private theorem normalizedSelected_mem_boundaryValues (v : V₀)
    (hv : v ∈ (diagonalChartSystem (E := E) h.pd p q).M I J)
    (hk : ∀ f : ExteriorDifferentials k E p →ₗ[F] F, tensorContraction f v = 0) :
    let T := diagonalChartSystem (E := E) h.pd p q
    v ∈ selectedBoundaryValues (k := k) (E := V₀) (T.M I J)
      (fun l => T.act (T.normalizedWeight n₀ T.homogeneousMinor i j l)) e₀ := by
  let T := diagonalChartSystem (E := E) h.pd p q
  let G := diagonalChartSystem_good (E := E) h.pd p q
  let A := diagonalChartSystem_admitted (E := E) h.pd p q
  letI chartAction : Module R₀ V₀ := tensorChartModule (rA k x I) (rA k x J)
  letI chartTower : IsScalarTower k R₀ V₀ := T.chartScalarTower
  let P : Submodule R₀ V₀ := projectiveTensorLattice (k := k) (E := E) (x := x) I J p q
  let r (l : DiagonalIndex d) : R₀ := ⟨T.normalizedWeight n₀ T.homogeneousMinor i j l,
    T.normalizedWeight_mem G A hi hj l⟩
  let a : P := ⟨v, hv⟩
  let w (l : DiagonalIndex d) : Module.End k V₀ :=
    T.act (T.normalizedWeight n₀ T.homogeneousMinor i j l)
  have hP : P.restrictScalars k = T.M I J := Submodule.ext fun _ => Iff.rfl
  have hw : (fun l => Algebra.lsmul k k V₀ (r l)) = w :=
    funext fun _ => LinearMap.ext fun _ => rfl
  exact @mem_selectedBoundaryValues_of_lattice_identification k R₀ V₀ (DiagonalIndex d)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    chartAction chartTower d P r (T.M I J) w hP hw e₀ a
    ((h.normalizedDiagonal_lattice p q hi hj).2 a hk)

include hi hj in
/-- Exactness of the full diagonal column and the criterion for a
closed column of top degree to be a boundary. -/
theorem IsFinCover.diagonalColumn_exact_and_boundary :
    let T := diagonalChartSystem (E := E) h.pd p q
    let C := T.columnComplex (fun _ => (1, 1)) (diagonalMinor (E := E) h.pd p q) I J
    (∀ n : ℤ, n < (d : ℤ) → C.Z n ≤ C.B n) ∧
    (∀ a ∈ C.Z (d : ℤ),
      (∀ f : ExteriorDifferentials k E p →ₗ[F] F,
        tensorContraction f (a (selectedIndices (diagonalIndexEmbedding j))) = 0) →
      a ∈ C.B (d : ℤ)) := by
  let T := diagonalChartSystem (E := E) h.pd p q
  let G := diagonalChartSystem_good (E := E) h.pd p q
  let A := diagonalChartSystem_admitted (E := E) h.pd p q
  let K (a : V₀) := ∀ f : ExteriorDifferentials k E p →ₗ[F] F, tensorContraction f a = 0
  have hunit (u : (F ⊗[k] F)ˣ) (v : V₀) (hv : K v) : K (T.act u v) := by
    intro f
    change tensorContraction f (tensorScalarAction (u : F ⊗[k] F) v) = 0
    rw [tensorContraction_action, hv f, smul_zero]
  exact T.columnExact_and_boundary_of_selected n₀ T.homogeneousMinor G A hi hj e₀ K hunit
    (normalizedSelected_exact h p q hi hj) (normalizedSelected_mem_boundaryValues h p q hi hj)

end GlobalTheory.PD
