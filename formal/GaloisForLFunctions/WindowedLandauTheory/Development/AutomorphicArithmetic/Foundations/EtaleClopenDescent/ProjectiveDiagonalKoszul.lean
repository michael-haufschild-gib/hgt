import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveCommonChartKoszul
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveTensorDenominator
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.KoszulScalarDescent

/-! Localizing the left lattice at the right coordinate reduces to a
common chart. The denominator is invertible modulo the selected weights,
so Koszul exactness and ideal membership descend. -/

noncomputable section

open GlobalTheory.CechDR GlobalTheory.SchemeCohomology GlobalTheory.WH
open scoped GlobalTheory.CechDR GlobalTheory.SchemeCohomology TensorProduct Pointwise

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
local notation "R₁" => tensorChartRing (rA k x (insert j I)) (rA k x J)

/-- On any nonempty chart pair, the selected weights are exact below
the relative dimension. They also generate every regular tensor
annihilated by diagonal contraction. -/
theorem IsFinCover.normalizedDiagonal_lattice :
    letI chartAction := tensorChartModule (V := ExteriorDifferentials k E p) (W := ExteriorDifferentials k E q)
      (rA k x I) (rA k x J)
    let P : Submodule R₀ V₀ := projectiveTensorLattice (k := k) (E := E) (x := x) I J p q
    letI : AddCommGroup P := @Submodule.addCommGroup R₀ V₀ inferInstance inferInstance chartAction P
    letI : Module R₀ P := @Submodule.module R₀ V₀ inferInstance inferInstance chartAction P
    let r := normalizedDiagonalWeights (E := E) h.pd p q hi hj
    (∀ (n : ℤ), n < (d : ℤ) → ∀ c : Finset (Fin d) → P,
      (∀ t : Finset (Fin d), (t.card : ℤ) ≠ n → c t = 0) →
      koszulDifferential r c = 0 → ∃ b : Finset (Fin d) → P,
        (∀ t : Finset (Fin d), (t.card : ℤ) ≠ n - 1 → b t = 0) ∧
          koszulDifferential r b = c) ∧
    (∀ t : P, (∀ f : ExteriorDifferentials k E p →ₗ[F] F, tensorContraction f (t : V₀) = 0) →
      t ∈ idealMultiple (M := P) (Ideal.span (Set.range r))) := by
  letI chartAction := tensorChartModule (V := ExteriorDifferentials k E p) (W := ExteriorDifferentials k E q)
    (rA k x I) (rA k x J)
  let P : Submodule R₀ V₀ := projectiveTensorLattice (k := k) (E := E) (x := x) I J p q
  letI : AddCommGroup P := @Submodule.addCommGroup R₀ V₀ inferInstance inferInstance chartAction P
  letI : Module R₀ P := @Submodule.module R₀ V₀ inferInstance inferInstance chartAction P
  let r : Fin d → R₀ := normalizedDiagonalWeights (E := E) h.pd p q hi hj
  by_cases hjI : j ∈ I
  · exact ⟨h.normalizedDiagonal_exact_common p q hi hj hjI,
      h.mem_normalizedDiagonal_smul_of_contraction_eq_zero_common p q hi hj hjI⟩
  letI enlargedAction : Module R₁ V₀ := tensorChartModule (rA k x (insert j I)) (rA k x J)
  letI : SMul R₀ V₀ := chartAction.toSMul
  letI : SMul R₁ V₀ := enlargedAction.toSMul
  have hI : I.Nonempty := ⟨i, hi⟩
  have hJ : J.Nonempty := ⟨j, hj⟩
  have hII : I ⊆ insert j I := Finset.subset_insert j I
  have hi' : i ∈ insert j I := hII hi
  have hj' : j ∈ insert j I := Finset.mem_insert_self _ _
  have hgood := diagonalChartSystem_good (E := E) h.pd p q
  have hR : (tensorChartRing (rA k x I) (rA k x J)) ≤
      tensorChartRing (rA k x (insert j I)) (rA k x J) :=
    hgood.monoR I (insert j I) J J hI hJ hII le_rfl
  letI chartInclusion : Algebra R₀ R₁ := (Subalgebra.inclusion hR).toRingHom.toAlgebra
  letI : SMul R₀ R₁ := chartInclusion.toSMul
  letI : IsScalarTower R₀ R₁ V₀ := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let P' : Submodule R₁ V₀ :=
    projectiveTensorLattice (k := k) (E := E) (x := x) (insert j I) J p q
  have hPQ : P ≤ P'.restrictScalars R₀ := by
    intro v hv
    exact hgood.monoM I (insert j I) J J hI hJ hII le_rfl hv
  let r' : Fin d → R₁ := normalizedDiagonalWeights (E := E) h.pd p q hi' hj
  have hmap : (fun l => algebraMap R₀ R₁ (r l)) = r' := funext fun _ => Subtype.ext rfl
  let a : R₀ := chartLeftCoordinate (k := k) (x := x) (J := J) hi j
  let b : R₀ := chartRightCoordinate (k := k) (x := x) (I := I) hj i
  have hab : 1 - a * b ∈ Ideal.span (Set.range r) :=
    one_sub_mul_mem_normalizedDiagonalWeights_span (E := E) h.pd p q hi hj
      (fun he => hjI (he ▸ hi))
  have hden (u : V₀) (hu : u ∈ P') :
      ∃ N : ℕ, tensorScalarAction ((a ^ N : R₀) : F ⊗[k] F) u ∈ P :=
    h.pd.exists_pow_smul_mem_projectiveTensorLattice_insert (J := J) (j := j) p q hi u hu
  let K (u : V₀) := ∀ f : ExteriorDifferentials k E p →ₗ[F] F, tensorContraction f u = 0
  exact koszul_exact_and_ideal_of_scalar_extension (R := R₀) (S := R₁) (V := V₀)
    P P' hPQ r r' hmap d hab hden K
    (h.normalizedDiagonal_exact_common p q hi' hj hj')
    (h.mem_normalizedDiagonal_smul_of_contraction_eq_zero_common p q hi' hj hj')

end GlobalTheory.PD
