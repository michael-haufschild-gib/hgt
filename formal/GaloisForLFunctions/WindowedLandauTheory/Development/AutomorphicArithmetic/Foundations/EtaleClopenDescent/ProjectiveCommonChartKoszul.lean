import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveDiagonalNormalizedIdeal
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveTensorLattice
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.KoszulWeaklyRegular

/-! The selected diagonal weights give exact Koszul cochains below
the relative dimension on chart pairs sharing the right denominator. -/

noncomputable section

open GlobalTheory.CechDR GlobalTheory.SchemeCohomology GlobalTheory.WH
open RingTheory.Sequence
open scoped GlobalTheory.CechDR GlobalTheory.SchemeCohomology TensorProduct Pointwise

namespace GlobalTheory.PD

variable {k F E : Type} [Field k] [CharZero k] [Field F] [Field E]
  [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
  {d : ℕ} {x : Fin (d + 1) → F} {I J : Finset (Fin (d + 1))} {i j : Fin (d + 1)}
  (h : IsFinCover k E x) (p q : ℕ) (hi : i ∈ I) (hj : j ∈ J) (hjI : j ∈ I)

local instance {r : ℕ} : IsScalarTower k F (ExteriorDifferentials k E r) :=
  IsScalarTower.to₁₂₄ k F E (ExteriorDifferentials k E r)

local notation "R₀" => tensorChartRing (rA k x I) (rA k x J)
local notation "V₀" => ExteriorDifferentials k E p ⊗[k] ExteriorDifferentials k E q

include hjI in
/-- Exactness of the selected diagonal Koszul cube on a chart pair
with a common denominator follows from the affine coordinate differences. -/
theorem IsFinCover.normalizedDiagonal_exact_common (n : ℤ) (hn : n < (d : ℤ)) :
    letI chartAction := tensorChartModule (V := ExteriorDifferentials k E p) (W := ExteriorDifferentials k E q)
      (rA k x I) (rA k x J)
    let Γ : Submodule R₀ V₀ := projectiveTensorLattice (k := k) (E := E) (x := x) I J p q
    letI : AddCommGroup Γ := @Submodule.addCommGroup R₀ V₀ inferInstance inferInstance chartAction Γ
    letI : Module R₀ Γ := @Submodule.module R₀ V₀ inferInstance inferInstance chartAction Γ
    let r := normalizedDiagonalWeights (E := E) h.pd p q hi hj
    ∀ c : Finset (Fin d) → Γ,
      (∀ t : Finset (Fin d), (t.card : ℤ) ≠ n → c t = 0) →
      koszulDifferential r c = 0 → ∃ b : Finset (Fin d) → Γ,
        (∀ t : Finset (Fin d), (t.card : ℤ) ≠ n - 1 → b t = 0) ∧ koszulDifferential r b = c := by
  letI chartAction := tensorChartModule (V := ExteriorDifferentials k E p) (W := ExteriorDifferentials k E q)
    (rA k x I) (rA k x J)
  let Γ : Submodule R₀ V₀ := projectiveTensorLattice (k := k) (E := E) (x := x) I J p q
  letI : AddCommGroup Γ := @Submodule.addCommGroup R₀ V₀ inferInstance inferInstance chartAction Γ
  letI : Module R₀ Γ := @Submodule.module R₀ V₀ inferInstance inferInstance chartAction Γ
  let r := normalizedDiagonalWeights (E := E) h.pd p q hi hj
  let z := h.pd.chartDiagonalGenerators hjI hj
  obtain ⟨hr, hk⟩ := h.pd.chartDiagonalGenerators_regular_kernel hjI hj
  have hreg : IsWeaklyRegular Γ (List.ofFn z) :=
    h.weaklyRegular_tensorLattice I J p q ⟨i, hi⟩ ⟨j, hj⟩ hr
  have hspan : Ideal.span (Set.range r) = Ideal.span (Set.range z) :=
    (normalizedDiagonalWeights_span (E := E) h.pd p q hi hj hjI).trans hk
  have hz : ∀ a ∈ List.ofFn z, a ∈ Ideal.span (Set.range r) := by
    intro a ha
    rw [hspan]
    exact Ideal.subset_span (by simpa only [List.mem_ofFn, Set.mem_range] using ha)
  have hn' : n < (List.ofFn z).length := by simpa only [List.length_ofFn] using hn
  exact koszul_exact_of_weaklyRegular r (List.ofFn z) hz Γ hreg n hn'

include hjI in
/-- On chart pairs with a common denominator, a tensor killed by all
diagonal contractions lies in the ideal of selected weights times the lattice. -/
theorem IsFinCover.mem_normalizedDiagonal_smul_of_contraction_eq_zero_common :
    letI chartAction := tensorChartModule (V := ExteriorDifferentials k E p) (W := ExteriorDifferentials k E q)
      (rA k x I) (rA k x J)
    let Γ : Submodule R₀ V₀ := projectiveTensorLattice (k := k) (E := E) (x := x) I J p q
    letI : AddCommGroup Γ := @Submodule.addCommGroup R₀ V₀ inferInstance inferInstance chartAction Γ
    letI : Module R₀ Γ := @Submodule.module R₀ V₀ inferInstance inferInstance chartAction Γ
    ∀ t : Γ, (∀ f : ExteriorDifferentials k E p →ₗ[F] F,
      tensorContraction f (t : ExteriorDifferentials k E p ⊗[k] ExteriorDifferentials k E q) = 0) →
      t ∈ idealMultiple (M := Γ)
        (Ideal.span (Set.range (normalizedDiagonalWeights (E := E) h.pd p q hi hj))) := by
  letI chartAction := tensorChartModule (V := ExteriorDifferentials k E p) (W := ExteriorDifferentials k E q)
    (rA k x I) (rA k x J)
  let Γ : Submodule R₀ V₀ := projectiveTensorLattice (k := k) (E := E) (x := x) I J p q
  letI : AddCommGroup Γ := @Submodule.addCommGroup R₀ V₀ inferInstance inferInstance chartAction Γ
  letI : Module R₀ Γ := @Submodule.module R₀ V₀ inferInstance inferInstance chartAction Γ
  suffices ∀ t : Γ, (∀ f : ExteriorDifferentials k E p →ₗ[F] F,
      tensorContraction f (t : V₀) = 0) →
      t ∈ idealMultiple (M := Γ)
        (Ideal.span (Set.range (normalizedDiagonalWeights (E := E) h.pd p q hi hj))) from this
  intro t ht
  rw [normalizedDiagonalWeights_span (E := E) h.pd p q hi hj hjI]
  exact h.mem_diagonalIdeal_tensorLattice_of_contraction_eq_zero I J p q ⟨i, hi⟩ ⟨j, hj⟩ t ht

end GlobalTheory.PD
