import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveFormDualFamily
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.TensorLatticeDiagonalKernel
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveDiagonalSystem

/-! The regular form lattice of a projective chart pair is projective
over its scalar tensor ring. Its diagonal ideal is detected by contraction. -/

noncomputable section

open GlobalTheory.CechDR GlobalTheory.SchemeCohomology
open RingTheory.Sequence
open scoped GlobalTheory.CechDR GlobalTheory.SchemeCohomology TensorProduct Pointwise

namespace GlobalTheory.PD

variable {k F E : Type} [Field k] [CharZero k] [Field F] [Field E]
  [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
  {d : ℕ} {x : Fin (d + 1) → F}
  (I J : Finset (Fin (d + 1))) (p q : ℕ)

local instance {r : ℕ} : IsScalarTower k F (ExteriorDifferentials k E r) :=
  IsScalarTower.to₁₂₄ k F E (ExteriorDifferentials k E r)

/-- The regular form tensors viewed over the chart tensor ring. -/
abbrev projectiveTensorLattice :
    letI chartAction := tensorChartModule (V := ExteriorDifferentials k E p) (W := ExteriorDifferentials k E q)
      (rA k x I) (rA k x J)
    Submodule (tensorChartRing (rA k x I) (rA k x J))
      (ExteriorDifferentials k E p ⊗[k] ExteriorDifferentials k E q) :=
  tensorChartSubmodule (smul_mem_regularExteriorLattice I p) (smul_mem_regularExteriorLattice J q)

variable (h : IsFinCover k E x) (hI : I.Nonempty) (hJ : J.Nonempty)

local notation "R₀" => tensorChartRing (rA k x I) (rA k x J)
local notation "V₀" => ExteriorDifferentials k E p ⊗[k] ExteriorDifferentials k E q

include h hI hJ in
/-- The regular form tensors on a chart pair are projective over the
chart tensor ring by the integral dual families on each factor. -/
theorem IsFinCover.projective_tensorLattice :
    letI chartAction := tensorChartModule (V := ExteriorDifferentials k E p) (W := ExteriorDifferentials k E q)
      (rA k x I) (rA k x J)
    Module.Projective (tensorChartRing (rA k x I) (rA k x J))
      (projectiveTensorLattice (k := k) (E := E) (x := x) I J p q) := by
  obtain ⟨_, v, φ, hv, hφ, hV⟩ := h.exists_formDualFamily_intersection hI p
  obtain ⟨_, w, ψ, hw, hψ, hW⟩ := h.exists_formDualFamily_intersection hJ q
  exact tensorChartSubmodule_projective (smul_mem_regularExteriorLattice I p)
    (smul_mem_regularExteriorLattice J q) v w φ ψ hv hw hφ hψ hV hW

include h hI hJ in
/-- A weakly regular sequence of chart scalars remains weakly regular
on the projective lattice of regular form tensors. -/
theorem IsFinCover.weaklyRegular_tensorLattice
    {r : List (tensorChartRing (rA k x I) (rA k x J))}
    (hr : IsWeaklyRegular (tensorChartRing (rA k x I) (rA k x J)) r) :
    letI chartAction := tensorChartModule (V := ExteriorDifferentials k E p) (W := ExteriorDifferentials k E q)
      (rA k x I) (rA k x J)
    let L : Submodule R₀ V₀ := projectiveTensorLattice (k := k) (E := E) (x := x) I J p q
    letI : AddCommGroup L := @Submodule.addCommGroup R₀ V₀ inferInstance inferInstance chartAction L
    letI : Module R₀ L := @Submodule.module R₀ V₀ inferInstance inferInstance chartAction L
    IsWeaklyRegular L r := by
  letI chartAction := tensorChartModule (V := ExteriorDifferentials k E p) (W := ExteriorDifferentials k E q)
    (rA k x I) (rA k x J)
  let L : Submodule R₀ V₀ := projectiveTensorLattice (k := k) (E := E) (x := x) I J p q
  letI : AddCommGroup L := @Submodule.addCommGroup R₀ V₀ inferInstance inferInstance chartAction L
  letI : Module R₀ L := @Submodule.module R₀ V₀ inferInstance inferInstance chartAction L
  letI : Module.Projective R₀ L := h.projective_tensorLattice I J p q hI hJ
  letI : Module.Flat R₀ L := Module.Flat.of_projective (R := R₀) (M := L)
  exact ((TensorProduct.rid R₀ L).isWeaklyRegular_congr r).mp hr.isWeaklyRegular_lTensor

include h hI hJ in
/-- A regular chart tensor contracting to zero against every
coordinate functional lies in the diagonal ideal times the lattice. -/
theorem IsFinCover.mem_diagonalIdeal_tensorLattice_of_contraction_eq_zero :
    letI chartAction := tensorChartModule (V := ExteriorDifferentials k E p) (W := ExteriorDifferentials k E q)
      (rA k x I) (rA k x J)
    let L : Submodule R₀ V₀ := projectiveTensorLattice (k := k) (E := E) (x := x) I J p q
    letI : AddCommGroup L := @Submodule.addCommGroup R₀ V₀ inferInstance inferInstance chartAction L
    letI : Module R₀ L := @Submodule.module R₀ V₀ inferInstance inferInstance chartAction L
    ∀ t : L, (∀ f : ExteriorDifferentials k E p →ₗ[F] F,
      tensorContraction f (t : ExteriorDifferentials k E p ⊗[k] ExteriorDifferentials k E q) = 0) →
      t ∈ idealMultiple (M := L)
        (RingHom.ker (tensorChartRingDiagonal (rA k x I) (rA k x J)).toRingHom) := by
  obtain ⟨_, v, φ, hv, hφ, hV⟩ := h.exists_formDualFamily_intersection hI p
  obtain ⟨_, w, ψ, hw, hψ, hW⟩ := h.exists_formDualFamily_intersection hJ q
  exact mem_diagonal_ideal_smul_of_tensorContraction_eq_zero
    (smul_mem_regularExteriorLattice I p) (smul_mem_regularExteriorLattice J q)
    v w φ ψ hv hw hφ hψ hV hW

end GlobalTheory.PD
