import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveDiagonalNormalizedIdeal
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveTensorLattice
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.FormSingleChartLocalization
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.TensorLatticeDenominator

/-! For a tensor regular after adding a left chart index, a power of
the corresponding left coordinate ratio gives a tensor on the original pair. -/

noncomputable section

open GlobalTheory.CechDR GlobalTheory.SchemeCohomology
open scoped GlobalTheory.CechDR GlobalTheory.SchemeCohomology TensorProduct

namespace GlobalTheory.PD

variable {k F E : Type} [Field k] [CharZero k] [Field F] [Field E]
  [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
  {d : ℕ} {x : Fin (d + 1) → F} {I J : Finset (Fin (d + 1))} {i j : Fin (d + 1)}

local instance {r : ℕ} : IsScalarTower k F (ExteriorDifferentials k E r) :=
  IsScalarTower.to₁₂₄ k F E (ExteriorDifferentials k E r)

/-- A single left coordinate ratio clears the denominators of each
regular tensor on an enlarged chart pair. -/
theorem IsPd.exists_pow_smul_mem_projectiveTensorLattice_insert (h : IsPd k x)
    (p q : ℕ) (hi : i ∈ I) (t : ExteriorDifferentials k E p ⊗[k] ExteriorDifferentials k E q)
    (ht : t ∈ projectiveTensorLattice (k := k) (E := E) (x := x) (insert j I) J p q) :
    let a := chartLeftCoordinate (k := k) (x := x) (J := J) hi j
    ∃ N : ℕ, tensorScalarAction ((a ^ N : tensorChartRing (rA k x I) (rA k x J)) : F ⊗[k] F) t ∈
      projectiveTensorLattice (k := k) (E := E) (x := x) I J p q := by
  let P := regularExteriorLattice (rB k E x I) p
  let P' := regularExteriorLattice (rB k E x (insert j I)) p
  let Q := regularExteriorLattice (rB k E x J) q
  have ha : x j / x i ∈ rA k x I := Algebra.subset_adjoin ⟨i, hi, j, rfl⟩
  have hP (v : ExteriorDifferentials k E p) (hv : v ∈ P) : (x j / x i) • v ∈ P :=
    smul_mem_regularExteriorLattice I p _ ha v hv
  have hden (v : ExteriorDifferentials k E p) (hv : v ∈ P') :
      ∃ N : ℕ, (x j / x i) ^ N • v ∈ P := by
    obtain ⟨N, hN⟩ := h.exists_smul_mem_omB_of_insert hi j v hv
    refine ⟨N, ?_⟩
    change algebraMap F E ((x j / x i) ^ N) • (v : DR k E) ∈ omB k E (rB k E x I) p
    simpa only [map_pow] using hN
  have ht' : t ∈ tensorChartLattice P' Q := ht
  obtain ⟨N, hN⟩ := exists_pow_left_mem_tensorChartLattice hP hden ht'
  refine ⟨N, ?_⟩
  let a := chartLeftCoordinate (k := k) (x := x) (J := J) hi j
  change tensorScalarAction ((a ^ N : tensorChartRing (rA k x I) (rA k x J)) : F ⊗[k] F) t ∈
    tensorChartLattice P Q
  have he : ((a ^ N : tensorChartRing (rA k x I) (rA k x J)) : F ⊗[k] F) =
      ((x j / x i) ^ N) ⊗ₜ[k] (1 : F) := by
    rw [Subalgebra.coe_pow, show (a : F ⊗[k] F) = (x j / x i) ⊗ₜ[k] (1 : F) from
      chartLeftCoordinate_coe (J := J) hi j, Algebra.TensorProduct.tmul_pow, one_pow]
  rwa [he]

end GlobalTheory.PD
