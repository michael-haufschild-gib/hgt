import DifferentialGeometry.Tensor.Exterior.Cochain
import GaloisForLFunctions.HTGeometry.CochainComplexCohomology
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Smooth manifold de Rham cohomology

The actual exterior derivative supplies the local cochain differential. Smooth
pullbacks induce contravariant maps on quotient cohomology. Above tangent dimension,
alternation forces every form to vanish; top-degree forms are therefore closed.
-/

noncomputable section
open Bundle Manifold
open scoped Manifold ContDiff
namespace HTGeometry.SmoothDeRham
open DifferentialGeometry
attribute [local instance] normedSpaceTangentSpace

variable {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  {HM : Type*} [TopologicalSpace HM] {IM : ModelWithCorners ℝ EM HM}
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M] [IsManifold IM ∞ M]

def complex [BoundarylessManifold IM M] :
    DeningerCochainComplex ℝ (DifferentialForm IM M) where
  d := DifferentialForm.exteriorDerivativeLinearMap
  d_comp_d n := by
    apply LinearMap.ext
    intro α
    exact DifferentialForm.exteriorDerivative_sq α

variable {EN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  {HN : Type*} [TopologicalSpace HN] {IN : ModelWithCorners ℝ EN HN}
  {N : Type*} [TopologicalSpace N] [ChartedSpace HN N] [IsManifold IN ∞ N]
  {EP : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
  {HP : Type*} [TopologicalSpace HP] {IP : ModelWithCorners ℝ EP HP}
  {P : Type*} [TopologicalSpace P] [ChartedSpace HP P] [IsManifold IP ∞ P]

variable [BoundarylessManifold IM M] [BoundarylessManifold IN N] [BoundarylessManifold IP P]

def pullback (f : M → N) (hf : ContMDiff IM IN ∞ f) :
    DeningerCochainMap (complex (IM := IN) (M := N)) (complex (IM := IM) (M := M)) where
  f := DifferentialForm.pullbackLinearMap f hf
  comm n := by
    apply LinearMap.ext
    intro α
    exact DifferentialForm.exteriorDerivative_pullback f hf α

theorem pullback_id :
    pullback (id : M → M) (contMDiff_id (I := IM)) =
      deningerCochainMapId (complex (IM := IM) (M := M)) := by
  unfold pullback deningerCochainMapId
  congr 1
  funext n
  apply LinearMap.ext
  intro α
  exact DifferentialForm.pullback_id α

theorem pullback_comp (f : M → N) (hf : ContMDiff IM IN ∞ f)
    (g : N → P) (hg : ContMDiff IN IP ∞ g) :
    pullback (g ∘ f) (hg.comp hf) = deningerCochainMapComp (pullback f hf) (pullback g hg) := by
  unfold pullback deningerCochainMapComp
  congr 1
  funext n
  apply LinearMap.ext
  intro α
  exact DifferentialForm.pullback_comp f hf g hg α

/-- Pullback on the local quotient cohomology of actual smooth forms. -/
def cohomologyPullback (f : M → N) (hf : ContMDiff IM IN ∞ f) (k : ℕ) :
    (complex (IM := IN) (M := N)).cohomology k →ₗ[ℝ]
      (complex (IM := IM) (M := M)).cohomology k :=
  (pullback f hf).cohomologyMap k

theorem cohomologyPullback_id (k : ℕ) :
    cohomologyPullback (id : M → M) (contMDiff_id (I := IM)) k = LinearMap.id := by
  unfold cohomologyPullback
  rw [pullback_id, deningerCochainMapId_cohomologyMap]

theorem cohomologyPullback_comp (f : M → N) (hf : ContMDiff IM IN ∞ f)
    (g : N → P) (hg : ContMDiff IN IP ∞ g) (k : ℕ) :
    cohomologyPullback (g ∘ f) (hg.comp hf) k =
      (cohomologyPullback f hf k).comp (cohomologyPullback g hg k) := by
  unfold cohomologyPullback
  rw [pullback_comp f hf g hg, deningerCochainMapComp_cohomologyMap]

omit [BoundarylessManifold IM M] in
theorem differentialForm_eq_zero_of_finrank_lt [FiniteDimensional ℝ EM]
    {k : ℕ} (hk : Module.finrank ℝ EM < k) (α : DifferentialForm IM M k) : α = 0 := by
  apply ContMDiffSection.ext
  intro x
  apply ContinuousAlternatingMap.ext
  intro v
  change (α x).toAlternatingMap v = 0
  apply AlternatingMap.map_linearDependent
  intro hv
  have hb := hv.fintype_card_le_finrank
  have he : Module.finrank ℝ (TangentSpace IM x) = Module.finrank ℝ EM := rfl
  rw [he, Fintype.card_fin] at hb
  exact (Nat.not_le_of_lt hk) hb

theorem topDegree_closed [FiniteDimensional ℝ EM]
    (α : DifferentialForm IM M (Module.finrank ℝ EM)) :
    DifferentialForm.exteriorDerivative α = 0 :=
  differentialForm_eq_zero_of_finrank_lt (Nat.lt_succ_self _) _

theorem cohomology_subsingleton_of_finrank_lt [FiniteDimensional ℝ EM]
    {k : ℕ} (hk : Module.finrank ℝ EM < k) :
    Subsingleton ((complex (IM := IM) (M := M)).cohomology k) := by
  letI : Subsingleton (DifferentialForm IM M k) := ⟨fun α β => by
    rw [differentialForm_eq_zero_of_finrank_lt hk α, differentialForm_eq_zero_of_finrank_lt hk β]⟩
  infer_instance

end HTGeometry.SmoothDeRham
