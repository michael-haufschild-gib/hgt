import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.TensorLatticeCoordinates
import Mathlib.LinearAlgebra.Pi
import Mathlib.RingTheory.Finiteness.Projective
import Mathlib.RingTheory.Ideal.Operations

/-! The integral tensor lattice is finite projective over the chart
tensor ring, and chart ideal membership is tested coordinatewise. -/

noncomputable section

open scoped TensorProduct Pointwise

namespace GlobalTheory.PD

variable {k F V W : Type*} [Field k] [Field F] [Algebra k F]
  [AddCommGroup V] [Module k V] [Module F V] [IsScalarTower k F V]
  [AddCommGroup W] [Module k W] [Module F W] [IsScalarTower k F W]
  {A B : Subalgebra k F} {P : Submodule k V} {Q : Submodule k W}

/-- Restrict the tensor scalar action to the chart tensor ring. -/
abbrev tensorChartModule (A B : Subalgebra k F) : Module (tensorChartRing A B) (V ⊗[k] W) :=
  Module.compHom (V ⊗[k] W)
    ((tensorScalarAction (V := V) (W := W)).comp (tensorChartRing A B).val).toRingHom

/-- The tensor lattice as a module over the chart tensor ring. -/
def tensorChartSubmodule
    (hP : ∀ a ∈ A, ∀ v ∈ P, a • v ∈ P) (hQ : ∀ b ∈ B, ∀ w ∈ Q, b • w ∈ Q) :
    letI := tensorChartModule (V := V) (W := W) A B
    Submodule (tensorChartRing A B) (V ⊗[k] W) :=
  letI := tensorChartModule (V := V) (W := W) A B
  { toAddSubmonoid := (tensorChartLattice P Q).toAddSubmonoid
    smul_mem' := fun s _ ht => tensorScalarAction_mem_chartLattice hP hQ s.property ht }

variable (hP : ∀ a ∈ A, ∀ v ∈ P, a • v ∈ P) (hQ : ∀ b ∈ B, ∀ w ∈ Q, b • w ∈ Q)

local notation "R" => tensorChartRing A B
local notation "Γ" => tensorChartSubmodule hP hQ

private def integralTensorCoordinate (φ : V →ₗ[F] F) (ψ : W →ₗ[F] F)
    (hφ : ∀ v ∈ P, φ v ∈ A) (hψ : ∀ w ∈ Q, ψ w ∈ B) :
    letI := tensorChartModule (V := V) (W := W) A B
    Γ →ₗ[R] R :=
  letI := tensorChartModule (V := V) (W := W) A B
  { toFun := fun t => ⟨tensorCoordinates φ ψ (t : V ⊗[k] W),
      tensorCoordinates_mem_chartRing hφ hψ t.property⟩
    map_add' := fun t u => Subtype.ext (map_add _ (t : V ⊗[k] W) (u : V ⊗[k] W))
    map_smul' := fun s t => Subtype.ext (tensorCoordinates_action φ ψ (s : F ⊗[k] F) (t : V ⊗[k] W)) }

variable {ι κ : Type*} [Fintype ι] [Fintype κ]
  (v : ι → V) (w : κ → W) (φ : ι → V →ₗ[F] F) (ψ : κ → W →ₗ[F] F)
  (hv : ∀ i, v i ∈ P) (hw : ∀ j, w j ∈ Q)

private def latticeTensor (i : ι) (j : κ) :
    letI := tensorChartModule (V := V) (W := W) A B
    Γ :=
  letI := tensorChartModule (V := V) (W := W) A B
  ⟨v i ⊗ₜ[k] w j, Submodule.apply_mem_map₂ _ (hv i) (hw j)⟩

include hv hw in
/-- Tensoring the two finite dual families gives a splitting of a
finite free module over the chart tensor ring. -/
theorem tensorChartSubmodule_projective
    (hφ : ∀ i a, a ∈ P → φ i a ∈ A) (hψ : ∀ j b, b ∈ Q → ψ j b ∈ B)
    (hV : ∀ a, a = ∑ i, φ i a • v i) (hW : ∀ b, b = ∑ j, ψ j b • w j) :
    letI := tensorChartModule (V := V) (W := W) A B
    Module.Projective R Γ := by
  letI := tensorChartModule (V := V) (W := W) A B
  let f : Γ →ₗ[R] ((ι × κ) → R) :=
    LinearMap.pi fun a => integralTensorCoordinate hP hQ (φ a.1) (ψ a.2) (hφ a.1) (hψ a.2)
  let g : ((ι × κ) → R) →ₗ[R] Γ :=
    ∑ i, ∑ j, (LinearMap.proj (i, j)).smulRight (latticeTensor hP hQ v w hv hw i j)
  refine Module.Projective.of_split f g (LinearMap.ext fun t => Subtype.ext ?_)
  change ((g (f t) : Γ) : V ⊗[k] W) = (t : V ⊗[k] W)
  simp only [g, f, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.proj_apply,
    LinearMap.pi_apply, Submodule.coe_sum, Submodule.coe_smul]
  exact (tensorCoordinates_sum v w φ ψ hV hW (t : V ⊗[k] W)).symm

include hv hw in
/-- A tensor lies in an ideal multiple of the lattice whenever all
of its integral dual coordinates lie in that ideal. -/
theorem mem_ideal_smul_tensorChartSubmodule
    (hφ : ∀ i a, a ∈ P → φ i a ∈ A) (hψ : ∀ j b, b ∈ Q → ψ j b ∈ B)
    (hV : ∀ a, a = ∑ i, φ i a • v i) (hW : ∀ b, b = ∑ j, ψ j b • w j) :
    letI := tensorChartModule (V := V) (W := W) A B
    ∀ (I : Ideal R) (t : Γ),
      (∀ i j, integralTensorCoordinate hP hQ (φ i) (ψ j) (hφ i) (hψ j) t ∈ I) →
        t ∈ I • (⊤ : Submodule R Γ) := by
  letI := tensorChartModule (V := V) (W := W) A B
  intro I t ht
  have hsum : t = ∑ i, ∑ j,
      integralTensorCoordinate hP hQ (φ i) (ψ j) (hφ i) (hψ j) t •
        latticeTensor hP hQ v w hv hw i j := by
    apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_smul]
    exact tensorCoordinates_sum v w φ ψ hV hW (t : V ⊗[k] W)
  rw [hsum]
  exact Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ =>
    Submodule.smul_mem_smul (ht i j) (Submodule.mem_top : latticeTensor hP hQ v w hv hw i j ∈ ⊤)

end GlobalTheory.PD
