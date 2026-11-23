import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.GenericChartForms

/-! Pullback on the exterior algebras of function fields. -/

noncomputable section

open GaloisForLFunctions.HTGeometry KaehlerDifferential
open GlobalTheory.SchemeCohomology
open scoped GlobalTheory.CechDR

namespace GlobalTheory.CechDR

variable {k E F : Type*} [Field k] [Field E] [Field F] [Algebra k E] [Algebra k F]
  (f : E →ₐ[k] F)

private abbrev targetAlgebra : Algebra E (DR k F) :=
  Algebra.compHom (DR k F) f.toRingHom

private theorem targetScalarTower :
    letI := targetAlgebra f
    IsScalarTower k E (DR k F) := by
  letI := targetAlgebra f
  refine IsScalarTower.of_algebraMap_eq fun c => ?_
  change algebraMap k (DR k F) c = algebraMap F (DR k F) (f (algebraMap k E c))
  rw [f.commutes, IsScalarTower.algebraMap_apply k F]

private def oneFormPullback :
    letI := targetAlgebra f
    Ω[E⁄k] →ₗ[E] DR k F :=
  letI := targetAlgebra f
  { toFun := fun ω => ExteriorAlgebra.ι F (algHomKaehlerMap f ω)
    map_add' := by intro ω η; rw [map_add, map_add]
    map_smul' := by
      intro c ω
      change ExteriorAlgebra.ι F (algHomKaehlerMap f (c • ω)) =
        f c • ExteriorAlgebra.ι F (algHomKaehlerMap f ω)
      rw [algHomKaehlerMap_smul, map_smul] }

private def pullbackDROver :
    letI := targetAlgebra f
    DR k E →ₐ[E] DR k F :=
  letI := targetAlgebra f
  ExteriorAlgebra.lift E
    ⟨oneFormPullback f, fun ω => ExteriorAlgebra.ι_sq_zero (algHomKaehlerMap f ω)⟩

/-- Pullback is the algebra map extending pullback on the coefficients and one-forms. -/
def pullbackDR : DR k E →ₐ[k] DR k F := by
  letI := targetAlgebra f
  letI := targetScalarTower f
  exact (pullbackDROver f).restrictScalars k

@[simp] theorem pullbackDR_ι (ω : Ω[E⁄k]) :
    pullbackDR f (ExteriorAlgebra.ι E ω) = ExteriorAlgebra.ι F (algHomKaehlerMap f ω) := by
  letI := targetAlgebra f
  change pullbackDROver f (ExteriorAlgebra.ι E ω) = oneFormPullback f ω
  exact ExteriorAlgebra.lift_ι_apply E (oneFormPullback f)
    (fun x => ExteriorAlgebra.ι_sq_zero (algHomKaehlerMap f x)) ω

theorem pullbackDR_smul (c : E) (x : DR k E) :
    pullbackDR f (c • x) = f c • pullbackDR f x := by
  letI := targetAlgebra f
  let g := pullbackDROver f
  change g (c • x) = f c • g x
  rw [Algebra.smul_def c x, map_mul, g.commutes]
  exact (Algebra.smul_def (f c) _).symm

theorem pullbackDR_wedge (p : ℕ) (v : Fin p → Ω[E⁄k]) :
    pullbackDR f (ExteriorAlgebra.ιMulti E p v) =
      ExteriorAlgebra.ιMulti F p (fun i => algHomKaehlerMap f (v i)) := by
  rw [ExteriorAlgebra.ιMulti_apply, ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_ofFn]
  apply congrArg List.prod
  apply congrArg List.ofFn
  funext i
  exact pullbackDR_ι f (v i)

theorem pullbackDR_degree (p : ℕ) (ω : ExteriorDifferentials k E p) :
    pullbackDR f (ω : DR k E) = (ExteriorDifferentials.map f p ω : DR k F) := by
  have hω : ω ∈ Submodule.span E (Set.range (exteriorPower.ιMulti E p (M := Ω[E⁄k]))) := by
    rw [exteriorPower.ιMulti_span]
    exact Submodule.mem_top
  induction hω using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    rw [ExteriorDifferentials.map_ιMulti, exteriorPower.ιMulti_apply_coe,
      exteriorPower.ιMulti_apply_coe, pullbackDR_wedge]
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [Submodule.coe_add, map_add, hx, hy]
  | smul c x _ hx =>
    simp only [Submodule.coe_smul_of_tower, LinearMap.map_smulₛₗ, pullbackDR_smul, hx]
    rfl

end GlobalTheory.CechDR

namespace GlobalTheory.PD

open GlobalTheory.CechDR

variable (k : Type*) [Field k] {E F : Type*} [Field E] [Field F] [Algebra k E] [Algebra k F]

/-- A map on rational forms acts on each coefficient and differential by the field map. -/
def IsDRMap (f : E →ₐ[k] F) (φ : DR k E →ₗ[k] DR k F) : Prop :=
  ∀ (p : ℕ) (b : E) (v : Fin p → E),
    φ (b • ExteriorAlgebra.ιMulti E p fun i => D k E (v i)) =
      f b • ExteriorAlgebra.ιMulti F p fun i => D k F (f (v i))

theorem isDRMap_pullbackDR (f : E →ₐ[k] F) : IsDRMap k f (pullbackDR f).toLinearMap := by
  intro p b v
  change pullbackDR f (b • ExteriorAlgebra.ιMulti E p (fun i => D k E (v i))) = _
  simp only [pullbackDR_smul, pullbackDR_wedge, algHomKaehlerMap_D]

theorem IsDRMap.regularForms {f : E →ₐ[k] F} {φ : DR k E →ₗ[k] DR k F}
    (hφ : IsDRMap k f φ) {A : Subalgebra k E} {B : Subalgebra k F} (h : A.map f ≤ B)
    (p : ℕ) : omB k E A p ≤ (omB k F B p).comap φ := by
  apply Submodule.span_le.mpr
  rintro _ ⟨b, hb, v, hv, rfl⟩
  change φ (b • ExteriorAlgebra.ιMulti E p (fun i => D k E (v i))) ∈ omB k F B p
  rw [hφ p b v]
  exact Submodule.subset_span
    ⟨f b, h ⟨b, hb, rfl⟩, fun i => f (v i), fun i => h ⟨v i, hv i, rfl⟩, rfl⟩

end GlobalTheory.PD
