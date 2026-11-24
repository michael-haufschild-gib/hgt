import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.GraphChartSystem
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveDiagonalAppendScaling

/-! On the graph, the homogeneous minors compare the two sets of
normalized coordinates. The additional weights compare affine generators. -/

noncomputable section

open GlobalTheory.CechDR GlobalTheory.WH.WeightedChartSystem
open scoped TensorProduct

namespace GlobalTheory.WH

open GlobalTheory.PD

variable {k F E L κ : Type} [Field k] [Field F] [Field E] [Field L] [LinearOrder κ]
  [Algebra k F] [Algebra k E] [Algebra k L] [Algebra F E] [Algebra E L] [Algebra F L]
  [IsScalarTower k F E] [IsScalarTower k E L] [IsScalarTower k F L] [IsScalarTower F E L]
  {d : ℕ} {x : Fin (d + 1) → F} (h : IsPd k x) (j₂ : E →ₐ[k] L) (q p : ℕ)
  (n : κ → ℕ × ℕ) (z : κ → E ⊗[k] E)

local notation "j₁" => IsScalarTower.toAlgHom k E L
local notation "T" => normalizedDiagonalSystem (E := E) h q p
local notation "U" => graphChartSystem h j₂ q p
local notation "g" => graphScalarMap (j₁) j₂
local notation "n₀" => (fun _ : DiagonalIndex d => ((1, 1) : ℕ × ℕ))

local notation "X" => fun a => algebraMap F L (x a)
local notation "Y" => fun a => j₂ (algebraMap F E (x a))

omit [IsScalarTower k F L] in
private theorem graphScalarMap_base_tmul (a b : F) :
    (g) (diagonalScalarMap (a ⊗ₜ[k] b)) = algebraMap F L a * j₂ (algebraMap F E b) := by
  rw [diagonalScalarMap, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.productMap_apply_tmul]
  change algebraMap E L (algebraMap F E a) * j₂ (algebraMap F E b) = _
  rw [← IsScalarTower.algebraMap_apply]

theorem graphChartSystem_X (i : Fin (d + 1)) : ((U).X i : L) = (X) i := by
  change (g) (((T).X i : (E ⊗[k] E)ˣ) : E ⊗[k] E) = _
  rw [normalizedDiagonalSystem_X, Algebra.TensorProduct.productMap_apply_tmul, map_one, mul_one]
  exact (IsScalarTower.algebraMap_apply F E L (x i)).symm

omit [IsScalarTower F E L] in
theorem graphChartSystem_Y (i : Fin (d + 1)) : ((U).Y i : L) = (Y) i := by
  change (g) (((T).Y i : (E ⊗[k] E)ˣ) : E ⊗[k] E) = _
  rw [normalizedDiagonalSystem_Y, Algebra.TensorProduct.productMap_apply_tmul, map_one, one_mul]

omit [LinearOrder κ] in
/-- Specializing a base minor gives the difference of products of the
two affine coordinate ratios. -/
theorem graph_normalizedMinor (i j a b : Fin (d + 1)) :
    let N : κ ⊕ₗ DiagonalIndex d → ℕ × ℕ := appendedDiagonalDegrees n
    let Z := appendedDiagonalWeights h q p z
    (U).normalizedWeight N ((g) ∘ Z) i j (toLex (Sum.inr (toLex (a, b)))) =
      ((X) a / (X) i) * ((Y) b / (Y) j) - ((X) b / (X) i) * ((Y) a / (Y) j) := by
  intro N Z
  let B := diagonalChartSystem (E := E) h q p
  have hb : (T).homogeneousMinor = diagonalScalarMap ∘ B.homogeneousMinor :=
    funext (normalizedDiagonalSystem_homogeneousMinor h q p)
  rw [graphChartSystem_normalizedWeight_map]
  change (g) ((T).normalizedWeight n₀ (T).homogeneousMinor i j (toLex (a, b))) = _
  rw [hb, normalizedDiagonalSystem_normalizedWeight, diagonalMinor_normalized, map_sub, map_sub,
    graphScalarMap_base_tmul, graphScalarMap_base_tmul]
  simp only [map_div₀]

/-- A function-field generator equation specializes to its two values
times a power of the right coordinate ratio. -/
theorem graph_normalizedGenerator (i j : Fin (d + 1)) (l : κ) (N : ℕ) (b : E)
    (hN : n l = (N, N))
    (hb : z l = (((T).X i ^ N * (T).Y i ^ N : (E ⊗[k] E)ˣ) : E ⊗[k] E) *
      (b ⊗ₜ[k] (1 : E) - (1 : E) ⊗ₜ[k] b)) :
    (U).normalizedWeight (appendedDiagonalDegrees n) ((g) ∘ appendedDiagonalWeights h q p z)
      i j (toLex (Sum.inl l)) = ((Y) i / (Y) j) ^ N * (algebraMap E L b - j₂ b) := by
  let N₁ : κ ⊕ₗ DiagonalIndex d → ℕ × ℕ := appendedDiagonalDegrees n
  let Z := appendedDiagonalWeights h q p z
  change (U).normalizedWeight N₁ ((g) ∘ Z) i j (toLex (Sum.inl l)) = _
  rw [graphChartSystem_normalizedWeight_map]
  change (g) (z l * ((((T).weightUnit n i j l)⁻¹ : (E ⊗[k] E)ˣ) : E ⊗[k] E)) = _
  rw [hb, weightUnit, hN]
  have hxi : (g) ((T).X i : E ⊗[k] E) = (X) i := graphChartSystem_X h j₂ q p i
  have hyi : (g) ((T).Y i : E ⊗[k] E) = (Y) i := graphChartSystem_Y h j₂ q p i
  have hyj : (g) ((T).Y j : E ⊗[k] E) = (Y) j := graphChartSystem_Y h j₂ q p j
  let u : (E ⊗[k] E)ˣ := (T).X i ^ N * (T).Y j ^ N
  have hu : (Units.map (g).toMonoidHom u : L) = ((X) i) ^ N * ((Y) j) ^ N := by
    change (g) (u : E ⊗[k] E) = _
    simp only [u, Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow, hxi, hyj]
  have hden : (g) ((u⁻¹ : (E ⊗[k] E)ˣ) : E ⊗[k] E) =
      (((X) i) ^ N * ((Y) j) ^ N)⁻¹ := by
    calc
      _ = (((Units.map (g).toMonoidHom u)⁻¹ : Lˣ) : L) := by
        rw [← map_inv]
        rfl
      _ = _ := by rw [Units.val_inv_eq_inv_val, hu]
  rw [map_mul]
  change (g) ((((T).X i ^ N * (T).Y i ^ N : (E ⊗[k] E)ˣ) : E ⊗[k] E) *
    (b ⊗ₜ[k] (1 : E) - (1 : E) ⊗ₜ[k] b)) * (g) ((u⁻¹ : (E ⊗[k] E)ˣ) : E ⊗[k] E) = _
  rw [hden]
  simp only [map_mul, Units.val_mul, Units.val_pow_eq_pow_val, map_pow, hxi, hyi, map_sub,
    Algebra.TensorProduct.productMap_apply_tmul, map_one, mul_one, one_mul]
  change ((X) i ^ N * (Y) i ^ N) * (algebraMap E L b - j₂ b) *
    ((X) i ^ N * (Y) j ^ N)⁻¹ = _
  have hx : (X) i ≠ 0 := (map_ne_zero _).mpr (h.ne i)
  have hy : (Y) j ≠ 0 := (map_ne_zero _).mpr ((map_ne_zero _).mpr (h.ne j))
  rw [div_pow]
  field_simp [hx, hy]

end GlobalTheory.WH
