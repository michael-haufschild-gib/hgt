import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.NormalizedDiagonalSystem

/-! Scalar extension preserves the normalization of homogeneous weights
and the regularity of the base diagonal equations on every chart pair. -/

noncomputable section

open GlobalTheory.CechDR GlobalTheory.SchemeCohomology GlobalTheory.WH
open GlobalTheory.WH.WeightedChartSystem
open scoped GlobalTheory.CechDR GlobalTheory.SchemeCohomology TensorProduct

namespace GlobalTheory.PD

variable {k F E : Type} [Field k] [Field F] [Field E]
  [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
  {d : ℕ} {x : Fin (d + 1) → F} (h : IsPd k x) (q p : ℕ)
  {κ : Type} [LinearOrder κ]

local notation "T" => diagonalChartSystem (E := E) h q p
local notation "W" => normalizedDiagonalSystem (E := E) h q p
local notation "f" => diagonalScalarMap (k := k) (F := F) (E := E)

theorem normalizedDiagonalSystem_weightUnit (n : κ → ℕ × ℕ)
    (i j : Fin (d + 1)) (l : κ) :
    (W).weightUnit n i j l = Units.map (f).toMonoidHom ((T).weightUnit n i j l) := by
  simp only [weightUnit, map_mul, map_pow]
  rfl

theorem normalizedDiagonalSystem_normalizedWeight (n : κ → ℕ × ℕ)
    (z : κ → F ⊗[k] F) (i j : Fin (d + 1)) (l : κ) :
    (W).normalizedWeight n (f ∘ z) i j l = f ((T).normalizedWeight n z i j l) := by
  rw [normalizedWeight, normalizedDiagonalSystem_weightUnit, ← map_inv, Units.coe_map,
    normalizedWeight, map_mul] <;> rfl

theorem normalizedDiagonalSystem_admitted_map (n : κ → ℕ × ℕ)
    (z : κ → F ⊗[k] F) (hz : (T).Admitted n z) : (W).Admitted n (f ∘ z) := by
  intro i j l
  rw [normalizedDiagonalSystem_normalizedWeight]
  exact diagonalScalarMap_mem (hz i j l)

omit [LinearOrder κ] in
theorem normalizedDiagonalSystem_homogeneousMinor (l : DiagonalIndex d) :
    (W).homogeneousMinor l = f ((T).homogeneousMinor l) := by
  simp only [homogeneousMinor, map_sub, map_mul]
  rfl

end GlobalTheory.PD
