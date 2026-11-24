import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.OriginColumnModels
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.GraphOriginSelectedWeights

/-! The left coordinates and the transverse graph coordinates give
point-local exactness tests for homogeneous top-form columns. -/

noncomputable section

open GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH.WeightedChartSystem
open scoped GlobalTheory.CechDR TensorProduct

namespace GlobalTheory.WH

variable {k F E L : Type} [Field k] [CharZero k] [IsAlgClosed k]
  [Field F] [Field E] [Field L]
  [Algebra k F] [Algebra k E] [Algebra k L] [Algebra F E] [Algebra F L] [Algebra E L]
  [IsScalarTower k F E] [IsScalarTower k F L] [IsScalarTower k E L] [IsScalarTower F E L]
  {d p q : ℕ} {x : Fin (d + 1) → F}
  (h : IsPd k x) (j₂ : E →ₐ[k] L) (hqp : q + p = d)
  (hL : IsFinCover k L x) [IsReduced ((rB k L x {0}) ⧸ originIdeal k L x)]
  {I J : Finset (Fin (d + 1))} {i j : Fin (d + 1)} (hi : i ∈ I) (hj : j ∈ J)

local notation "B" => RY x j₂ I J
local notation "B₀" => rB k L x {0}
local notation "T" => graphChartSystem h j₂ q p

variable [Algebra.FiniteType k (RY x j₂ I J)]

include hqp hL

/-- When the selected weights are the left coordinates, their common
origin model tests the boundaries of the full column. -/
theorem graphColumn_tests_of_originCoordinates {ι : Type} [LinearOrder ι] [Fintype ι]
    {n : ι → ℕ × ℕ} {z : ι → L} (hz : (T).Admitted n z) (sel : Fin d ↪o ι) :
    let r := graphColumnWeights h j₂ (q := q) (p := p) hi hj hz
    let w := fun l => Algebra.lsmul k k (DR k L) (r l : L)
    let C := (T).columnComplex n z I J
    (∀ m, (r (sel m) : L) = algebraMap F L (x m.succ / x i)) →
    (∀ e : B →ₐ[k] k, (∀ l, e (r l) = 0) → i = 0 ∧
      ∃ f : OriginFibrePoint k L x, ∀ a b, Val B e a b ↔ Val B₀ f.1 a b) →
    (∀ m < (d : ℤ), C.Z m ≤ C.B m) ∧
      ∀ a ∈ C.Z (d : ℤ),
        (∀ e : B →ₐ[k] k, (∀ l, e (r l) = 0) →
          ((T).scaleColumn n i j).symm a (selectedIndices sel) ∈
            selectedBoundaryValues (omB k L (loc B e) d) w sel) →
        a ∈ C.B (d : ℤ) := by
  intro r w C hr he
  refine graphColumn_exact_and_boundary_of_originModel h j₂ hqp hi hj hz sel hL ?_
  intro e hzero
  obtain ⟨hi₀, f, hval⟩ := he e hzero
  refine ⟨f, originColumn_model_of_localValues hL e f hval r sel ?_⟩
  intro m
  exact (hr m).trans (congrArg (fun l => algebraMap F L (x m.succ / x l)) hi₀)

variable {κ : Type} [LinearOrder κ] [Fintype κ]
  {n : κ → ℕ × ℕ} {z : κ → E ⊗[k] E} (hz : NormalizedDiagonalEquations h n z)

local notation "G" => κ ⊕ₗ DiagonalIndex d
local notation "nG" => (appendedDiagonalDegrees (d := d) n : G → ℕ × ℕ)
local notation "zG" => graphScalarMap (IsScalarTower.toAlgHom k E L) j₂ ∘ appendedDiagonalWeights h q p z
local notation "hG" => graphChartSystem_admitted_map h j₂ q p nG (appendedDiagonalWeights h q p z)
  (appendedDiagonal_admitted h q p hz)
local notation "Fixed" => fun f : OriginFibrePoint k L x => IsFix B₀ (Subtype.val f) j₂ (rB k E x {0})

/-- The selected graph differences give the same boundary test at a
fixed point where the transverse determinant is nonzero. -/
theorem graphColumn_tests_of_fixedOrigin
    (M : OriginFibrePoint k L x → Matrix (Fin d) (Fin d) k)
    (hrow : ∀ f, (Fixed) f → ∀ m, ∃ (c : B₀) (g : Fin d → B₀), f.1 c ≠ 0 ∧
      (c : L) * j₂ (algebraMap F E (x m.succ / x 0)) =
        ∑ l, (g l : L) * algebraMap F L (x l.succ / x 0) ∧
      ∀ l, f.1 (g l) = f.1 c * M f m l)
    (hdet : ∀ f, (Fixed) f → (1 - M f).det ≠ 0)
    (hzero : ∀ e : B →ₐ[k] k, (∀ l, e ⟨_, graphAffineWeight_mem h j₂ hz hi hj l⟩ = 0) →
      I = {0} ∧ J = {0} ∧
        ∃ f : OriginFibrePoint k L x, (Fixed) f ∧ ∀ a b, Val B e a b ↔ Val B₀ f.1 a b) :
    let r := graphColumnWeights h j₂ (q := q) (p := p) hi hj (hG)
    let w := fun l => Algebra.lsmul k k (DR k L) (r l : L)
    let C := (T).columnComplex nG (zG) I J
    (∀ m < (d : ℤ), C.Z m ≤ C.B m) ∧
      ∀ a ∈ C.Z (d : ℤ),
        (∀ e : B →ₐ[k] k, (∀ l, e (r l) = 0) →
          ((T).scaleColumn nG i j).symm a (selectedIndices (graphOriginSelection (κ := κ))) ∈
            selectedBoundaryValues (omB k L (loc B e) d) w graphOriginSelection) →
        a ∈ C.B (d : ℤ) := by
  intro r w C
  refine graphColumn_exact_and_boundary_of_originModel h j₂ hqp hi hj (hG) graphOriginSelection hL ?_
  intro e he
  obtain ⟨hI, hJ, f, hf, hval⟩ := hzero e he
  have hi₀ : i = 0 := Finset.mem_singleton.mp (hI ▸ hi)
  have hj₀ : j = 0 := Finset.mem_singleton.mp (hJ ▸ hj)
  subst i
  subst j
  obtain ⟨u, hu, hs⟩ := exists_graphOrigin_localWeights h j₂ hL hz f hf (M f) (hrow f hf) (hdet f hf)
  exact ⟨f, loc_eq_of_val_iff B e hval, u, hu, hs⟩

end GlobalTheory.WH
