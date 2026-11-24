import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.LogarithmicChartSystem
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveAffineIdentityTensor

/-! The trace of a left wedge product is formed before taking the
residue. This coefficient map commutes with the diagonal scalar action. -/

noncomputable section

open GlobalTheory.CechDR GlobalTheory.SchemeCohomology GlobalTheory.WH
open scoped GlobalTheory.CechDR GlobalTheory.SchemeCohomology TensorProduct

namespace GlobalTheory.PD

variable {k F E : Type} [Field k] [Field F] [Field E]
  [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
  {d : ℕ} {x : Fin (d + 1) → F} {p q : ℕ}

local instance {r : ℕ} : IsScalarTower k F (ExteriorDifferentials k E r) :=
  IsScalarTower.to₁₂₄ k F E (ExteriorDifferentials k E r)

local notation "V₀" => ExteriorDifferentials k E q
local notation "W₀" => ExteriorDifferentials k E p

/-- Pair a complementary left form against the input, and retain its
trace coefficient in the left tensor factor. -/
def traceWedgeTensorCoefficient (τ : DR k E →ₗ[E] E) :
    (V₀ ⊗[k] W₀) →ₗ[k] W₀ →ₗ[k] (F ⊗[k] W₀) := by
  let f : V₀ →ₗ[k] Module.Dual F W₀ := (traceWedgeLeftDual (F := F) τ).restrictScalars k
  refine TensorProduct.lift (LinearMap.mk₂ k (fun u v =>
    ((TensorProduct.mk k F W₀).flip v).comp ((f u).restrictScalars k)) ?_ ?_ ?_ ?_)
  · intro u v w
    refine LinearMap.ext fun a => ?_
    change (f (u + v) a) ⊗ₜ[k] w = (f u a) ⊗ₜ[k] w + (f v a) ⊗ₜ[k] w
    rw [map_add, LinearMap.add_apply, TensorProduct.add_tmul]
  · intro c u v
    refine LinearMap.ext fun a => ?_
    change (f (c • u) a) ⊗ₜ[k] v = c • ((f u a) ⊗ₜ[k] v)
    rw [map_smul, LinearMap.smul_apply, TensorProduct.smul_tmul']
  · intro u v w
    refine LinearMap.ext fun a => ?_
    exact TensorProduct.tmul_add (f u a) v w
  · intro c u v
    refine LinearMap.ext fun a => ?_
    exact TensorProduct.tmul_smul c (f u a) v

theorem traceWedgeTensorCoefficient_tmul (τ : DR k E →ₗ[E] E) (u : V₀) (v a : W₀) :
    traceWedgeTensorCoefficient τ (u ⊗ₜ[k] v) a =
      (traceWedgeLeftDual (F := F) τ u a) ⊗ₜ[k] v := by
  rw [traceWedgeTensorCoefficient, TensorProduct.lift.tmul]
  rfl

/-- The trace coefficient map commutes with the two rational coordinate
actions. -/
theorem traceWedgeTensorCoefficient_action (τ : DR k E →ₗ[E] E) (s : F ⊗[k] F)
    (t : V₀ ⊗[k] W₀) (a : W₀) :
    traceWedgeTensorCoefficient (F := F) τ (tensorScalarAction s t) a =
      tensorScalarAction (V := F) (W := W₀) s (traceWedgeTensorCoefficient (F := F) τ t a) := by
  induction s using TensorProduct.induction_on with
  | zero => simp
  | add s r hs hr => simp only [map_add, LinearMap.add_apply, hs, hr]
  | tmul b c =>
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add u v hu hv => simp only [map_add, LinearMap.add_apply, hu, hv]
    | tmul u v =>
      simp only [tensorScalarAction_tmul, traceWedgeTensorCoefficient_tmul,
        map_smul, LinearMap.smul_apply]

theorem collapseLogarithmicTensor_traceWedgeTensorCoefficient (τ : DR k E →ₗ[E] E)
    (t : V₀ ⊗[k] W₀) (a : W₀) :
    collapseLogarithmicTensor (k := k) (F := F) p (traceWedgeTensorCoefficient τ t a) =
      tensorContraction ((traceWedgeLeftDual (F := F) τ).flip a) t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv => simp only [map_add, LinearMap.add_apply, hu, hv]
  | tmul u v =>
    rw [traceWedgeTensorCoefficient_tmul, collapseLogarithmicTensor,
      tensorContraction_tmul, tensorContraction_tmul, LinearMap.id_apply, LinearMap.flip_apply]

variable [CharZero k]

/-- A regular input form multiplies the left chart coefficient on the
joined intersection and leaves the right chart regular. -/
theorem IsFinCover.traceWedgeTensorCoefficient_mem (h : IsFinCover k E x)
    (τ : DR k E →ₗ[E] E) (hτ : IsTop (x := x) τ) (hpq : p + q = d)
    {I J A : Finset (Fin (d + 1))} {a : W₀}
    (ha : a ∈ regularExteriorLattice (rB k E x A) p)
    {t : V₀ ⊗[k] W₀} (ht : t ∈ (diagonalChartSystem (E := E) h.pd q p).M I J) :
    traceWedgeTensorCoefficient τ t a ∈ (logarithmicChartSystem (E := E) h.pd p).M (I ∪ A) J := by
  refine (show (diagonalChartSystem (E := E) h.pd q p).M I J ≤
    ((logarithmicChartSystem (E := E) h.pd p).M (I ∪ A) J).comap
      ((traceWedgeTensorCoefficient τ).flip a) from Submodule.map₂_le.mpr ?_) ht
  intro u hu v hv
  change traceWedgeTensorCoefficient (F := F) τ (u ⊗ₜ[k] v) a ∈
    tensorChartLattice (logCoefficientLattice k x (I ∪ A)) (regularExteriorLattice (rB k E x J) p)
  rw [traceWedgeTensorCoefficient_tmul]
  apply Submodule.apply_mem_map₂ _ ?_ hv
  rw [traceWedgeLeftDual_apply]
  apply h.trace_logarithmic_coefficient_mem_lattice τ hτ
  let B := rB k E x (I ∪ A)
  have hm : (u : DR k E) * (a : DR k E) ∈ omB k E B (q + p) :=
    mul_mem_omB
      (omB_mono (rB_mono (E := E) (x := x) Finset.subset_union_left) q hu)
      (omB_mono (rB_mono (E := E) (x := x) Finset.subset_union_right) p ha)
  have hqp : q + p = d := (Nat.add_comm q p).trans hpq
  exact (congrArg (fun r => (u : DR k E) * (a : DR k E) ∈ omB k E B r) hqp).mp hm

end GlobalTheory.PD
