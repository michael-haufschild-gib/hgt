import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.LogarithmicTraceSection
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.LogarithmicChartSystem
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveDiagonalColumns
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.TensorChartMap
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.WeightedChartColumnMap

/-! The logarithmic columns are a retract of the regular form columns.
Consequently they have the same lower exactness and the top boundary
criterion is detected by collapsing the selected tensor value. -/

noncomputable section

open GlobalTheory.CechDR GlobalTheory.SchemeCohomology GlobalTheory.WH
open GlobalTheory.WH.WeightedChartSystem
open scoped GlobalTheory.CechDR GlobalTheory.SchemeCohomology TensorProduct

namespace GlobalTheory.PD

private theorem columnExact_of_retract {k M N : Type} [Field k]
    [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
    {C : Cx k M} {D : Cx k N} {f : M →ₗ[k] N} {g : N →ₗ[k] M}
    (hf : IsMap C D f) (hg : IsMap D C g) (hgf : Function.LeftInverse g f)
    (n : ℤ) {P : M → Prop} {Q : N → Prop} (hPQ : ∀ a, P a → Q (f a))
    (hE : ∀ m < n, D.Z m ≤ D.B m)
    (hB : ∀ a ∈ D.Z n, Q a → a ∈ D.B n) :
    (∀ m < n, C.Z m ≤ C.B m) ∧ (∀ a ∈ C.Z n, P a → a ∈ C.B n) := by
  have hcycles (m : ℤ) {a : M} (ha : a ∈ C.Z m) : f a ∈ D.Z m := by
    obtain ⟨hC, hD⟩ := hf m a ha.1
    exact ⟨hC, LinearMap.mem_ker.mpr
      (hD.symm.trans ((congrArg f (LinearMap.mem_ker.mp ha.2)).trans (map_zero f)))⟩
  have hboundary (m : ℤ) {a : M} (ha : f a ∈ D.B m) : a ∈ C.B m := by
    obtain ⟨y, hy, he⟩ := ha
    obtain ⟨hyC, hyD⟩ := hg (m - 1) y hy
    exact ⟨g y, hyC, hyD.symm.trans ((congrArg g he).trans (hgf a))⟩
  exact ⟨fun m hm a ha => hboundary m (hE m hm (hcycles m ha)),
    fun a ha hp => hboundary n (hB (f a) (hcycles n ha) (hPQ a hp))⟩

variable {k F E : Type} [Field k] [CharZero k] [Field F] [Field E]
  [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
  {d : ℕ} {x : Fin (d + 1) → F} {p : ℕ}

local instance {r : ℕ} : IsScalarTower k F (ExteriorDifferentials k E r) :=
  IsScalarTower.to₁₂₄ k F E (ExteriorDifferentials k E r)

local notation "W₀" => ExteriorDifferentials k E p
local notation "V₀" => ExteriorDifferentials k E d

omit [CharZero k] in
private theorem tensorContraction_scalarId (r : F) (t : F ⊗[k] W₀) :
    tensorContraction (r • (LinearMap.id : F →ₗ[F] F)) t =
      r • collapseLogarithmicTensor (k := k) (F := F) p t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, smul_add, ha, hb]
  | tmul a b =>
    simp only [collapseLogarithmicTensor, tensorContraction_tmul, LinearMap.smul_apply,
      LinearMap.id_apply, smul_eq_mul, mul_smul]

omit [CharZero k] in
private theorem tensorContraction_eq_zero_of_collapse (s : F →ₗ[F] V₀)
    (φ : V₀ →ₗ[F] F) (t : F ⊗[k] W₀)
    (ht : collapseLogarithmicTensor (k := k) (F := F) p t = 0) :
    tensorContraction φ (tensorMapLeft s t) = 0 := by
  have hφ : φ.comp s = φ (s 1) • (LinearMap.id : F →ₗ[F] F) := by
    apply LinearMap.ext
    intro a
    have hs : s a = a • s 1 := by rw [← map_smul, smul_eq_mul, mul_one]
    rw [LinearMap.comp_apply, hs, map_smul, LinearMap.smul_apply, LinearMap.id_apply,
      smul_eq_mul, smul_eq_mul, mul_comm]
  rw [tensorContraction_tensorMapLeft, hφ, tensorContraction_scalarId, ht, smul_zero]

/-- The logarithmic column is exact below the dimension, and collapse
detects when its selected component is a top boundary. -/
theorem IsFinCover.logarithmicColumn_exact_and_boundary (h : IsFinCover k E x)
    (τ : DR k E →ₗ[E] E) (hτ : IsTop (x := x) τ)
    {I J : Finset (Fin (d + 1))} {i j : Fin (d + 1)} (hi : i ∈ I) (hj : j ∈ J) :
    let T := logarithmicChartSystem (E := E) h.pd p
    let C := T.columnComplex (fun _ => (1, 1)) T.homogeneousMinor I J
    (∀ m : ℤ, m < (d : ℤ) → C.Z m ≤ C.B m) ∧
    (∀ a ∈ C.Z (d : ℤ), collapseLogarithmicTensor (k := k) (F := F) p
      (a (selectedIndices (diagonalIndexEmbedding j))) = 0 → a ∈ C.B (d : ℤ)) := by
  let T := logarithmicChartSystem (E := E) h.pd p
  let U := diagonalChartSystem (E := E) h.pd d p
  let n : DiagonalIndex d → ℕ × ℕ := fun _ => (1, 1)
  let z := T.homogeneousMinor
  let C := T.columnComplex n z I J
  let D := U.columnComplex n z I J
  obtain ⟨s, hs, hreg⟩ := h.exists_logarithmicTraceSection τ hτ
  let t : V₀ →ₗ[F] F := traceTopCoefficient τ
  let f : F ⊗[k] W₀ →ₗ[k] V₀ ⊗[k] W₀ := tensorMapLeft s
  let g : V₀ ⊗[k] W₀ →ₗ[k] F ⊗[k] W₀ := tensorMapLeft t
  let fC := mapCochain (ι := DiagonalIndex d) (M := F ⊗[k] W₀) (N := V₀ ⊗[k] W₀) f
  let gC := mapCochain (ι := DiagonalIndex d) (M := V₀ ⊗[k] W₀) (N := F ⊗[k] W₀) g
  have hfg : Function.LeftInverse g f := tensorMapLeft_leftInverse s t hs
  have hfM : T.M I J ≤ (U.M I J).comap f :=
    tensorMapLeft_mem s (fun _ hu => hreg I ⟨i, hi⟩ _ hu)
  have hgM : U.M I J ≤ (T.M I J).comap g :=
    tensorMapLeft_mem t (fun _ hu => h.traceTopCoefficient_mem τ hτ I hu)
  have hf : IsMap C D fC :=
    isMap_columnMap T U f rfl rfl (tensorMapLeft_action s) I J hfM n z
  have hg : IsMap D C gC :=
    isMap_columnMap U T g rfl rfl (tensorMapLeft_action t) I J hgM n z
  have hleft : Function.LeftInverse gC fC :=
    fun a => funext fun L => hfg (a L)
  let L := selectedIndices (diagonalIndexEmbedding j)
  let P (a : Finset (DiagonalIndex d) → F ⊗[k] W₀) :=
    collapseLogarithmicTensor (k := k) (F := F) p (a L) = 0
  let Q (a : Finset (DiagonalIndex d) → V₀ ⊗[k] W₀) :=
    ∀ φ : V₀ →ₗ[F] F, tensorContraction φ (a L) = 0
  have hPQ (a : Finset (DiagonalIndex d) → F ⊗[k] W₀) (ha : P a) : Q (fC a) :=
    fun φ => tensorContraction_eq_zero_of_collapse s φ (a L) ha
  have hED : (∀ m < (d : ℤ), D.Z m ≤ D.B m) ∧ (∀ a ∈ D.Z (d : ℤ), Q a → a ∈ D.B (d : ℤ)) :=
    h.diagonalColumn_exact_and_boundary d p hi hj
  exact columnExact_of_retract hf hg hleft (d : ℤ) hPQ hED.1 hED.2

end GlobalTheory.PD
