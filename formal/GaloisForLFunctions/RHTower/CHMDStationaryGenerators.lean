import GaloisForLFunctions.RHTower.CHMDStationaryOperatorDomain
import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-!
# Self-adjoint generators and the stationary bounded-perturbation identity

The injective Riesz resolvents define actual partially defined operators.
Their adjoints have the same domains: testing against every resolvent image
forces the resolvent equation for an arbitrary adjoint-domain vector.
The full arithmetic generator and the stationary theta-pullback generator
therefore share their exact operator domain and differ by the displayed bounded
prime-plus-potential operator. Compact operator-core density remains separate.
-/

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace
noncomputable section
namespace RHTower.CHMDDoobGraph
open CHMDPolar

section ResolventGenerator
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Invert an injective resolvent on its range, then subtract the identity. -/
def generatorOfResolvent (R : H →L[ℝ] H) (hR : Function.Injective R) :
    H →ₗ.[ℝ] H where
  domain := R.range
  toFun := (LinearEquiv.ofInjective R.toLinearMap hR).symm.toLinearMap - R.range.subtype

omit [CompleteSpace H] in
theorem generatorOfResolvent_apply (R : H →L[ℝ] H) (hR : Function.Injective R)
    (w : H) :
    generatorOfResolvent R hR ⟨R w, ⟨w, rfl⟩⟩ = w - R w := by
  change (LinearEquiv.ofInjective R.toLinearMap hR).symm ⟨R w, ⟨w, rfl⟩⟩ - R w = w - R w
  have h : (LinearEquiv.ofInjective R.toLinearMap hR).symm ⟨R w, ⟨w, rfl⟩⟩ = w := by
    apply hR
    exact LinearEquiv.ofInjective_symm_apply _ _
  rw [h]

omit [CompleteSpace H] in
theorem generatorOfResolvent_identity (R : H →L[ℝ] H) (hR : Function.Injective R)
    (u : (generatorOfResolvent R hR).domain) :
    R ((u : H) + generatorOfResolvent R hR u) = u := by
  change R ((u : H) + ((LinearEquiv.ofInjective R.toLinearMap hR).symm u - u)) = u
  have h : (u : H) + ((LinearEquiv.ofInjective R.toLinearMap hR).symm u - u) =
      (LinearEquiv.ofInjective R.toLinearMap hR).symm u := by abel
  rw [h]
  exact LinearEquiv.ofInjective_symm_apply _ _

theorem generatorOfResolvent_dense (R : H →L[ℝ] H) (hR : Function.Injective R)
    (hsa : IsSelfAdjoint R) : Dense ((generatorOfResolvent R hR).domain : Set H) := by
  change Dense (R.range : Set H)
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    R.orthogonal_range, hsa.adjoint_eq]
  exact LinearMap.ker_eq_bot.mpr hR

theorem generatorOfResolvent_formalSelfAdjoint (R : H →L[ℝ] H)
    (hR : Function.Injective R) (hsa : IsSelfAdjoint R) :
    (generatorOfResolvent R hR).IsFormalAdjoint (generatorOfResolvent R hR) := by
  rintro ⟨x, hx⟩ ⟨y, hy⟩
  obtain ⟨u, rfl⟩ := hx
  obtain ⟨v, rfl⟩ := hy
  have hs : ⟪R u, v⟫_ℝ = ⟪u, R v⟫_ℝ :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hsa u v
  erw [generatorOfResolvent_apply, generatorOfResolvent_apply, inner_sub_left, inner_sub_right, hs]
  rfl

theorem generatorOfResolvent_adjoint_identity (R : H →L[ℝ] H)
    (hR : Function.Injective R) (hsa : IsSelfAdjoint R)
    (u : (generatorOfResolvent R hR).adjoint.domain) :
    R ((u : H) + (generatorOfResolvent R hR).adjoint u) = u := by
  apply ext_inner_right ℝ
  intro z
  have h := LinearPMap.adjoint_isFormalAdjoint (generatorOfResolvent_dense R hR hsa)
    u ⟨R z, ⟨z, rfl⟩⟩
  rw [generatorOfResolvent_apply, inner_sub_right] at h
  have hs : ⟪R ((u : H) + (generatorOfResolvent R hR).adjoint u), z⟫_ℝ =
      ⟪(u : H) + (generatorOfResolvent R hR).adjoint u, R z⟫_ℝ :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hsa _ z
  rw [hs, inner_add_left]
  linarith

theorem generatorOfResolvent_isSelfAdjoint (R : H →L[ℝ] H)
    (hR : Function.Injective R) (hsa : IsSelfAdjoint R) :
    IsSelfAdjoint (generatorOfResolvent R hR) := by
  rw [LinearPMap.isSelfAdjoint_def]
  apply le_antisymm
  · refine ⟨?_, ?_⟩
    · intro u hu
      exact ⟨u + (generatorOfResolvent R hR).adjoint ⟨u, hu⟩,
        generatorOfResolvent_adjoint_identity R hR hsa ⟨u, hu⟩⟩
    · intro x y hxy
      have h := hR ((generatorOfResolvent_adjoint_identity R hR hsa x).trans
        (hxy.trans (generatorOfResolvent_identity R hR y).symm))
      rw [hxy] at h
      exact add_left_cancel h
  · exact (generatorOfResolvent_formalSelfAdjoint R hR hsa).le_adjoint
      (generatorOfResolvent_dense R hR hsa)

end ResolventGenerator

def arithmeticGenerator : MassSpace →ₗ.[ℝ] MassSpace :=
  generatorOfResolvent resolvent resolvent_injective

def stationaryGenerator : MassSpace →ₗ.[ℝ] MassSpace :=
  generatorOfResolvent stationaryResolvent stationaryResolvent_injective

theorem arithmeticGenerator_isSelfAdjoint : IsSelfAdjoint arithmeticGenerator :=
  generatorOfResolvent_isSelfAdjoint _ _ isSelfAdjoint_resolvent

theorem stationaryGenerator_isSelfAdjoint : IsSelfAdjoint stationaryGenerator :=
  generatorOfResolvent_isSelfAdjoint _ _ stationaryResolvent_isSelfAdjoint

theorem arithmeticGenerator_isClosed : arithmeticGenerator.IsClosed :=
  arithmeticGenerator_isSelfAdjoint.isClosed

theorem stationaryGenerator_isClosed : stationaryGenerator.IsClosed :=
  stationaryGenerator_isSelfAdjoint.isClosed

theorem arithmeticGenerator_resolvent (w : MassSpace) :
    arithmeticGenerator ⟨resolvent w, ⟨w, rfl⟩⟩ = w - resolvent w :=
  generatorOfResolvent_apply _ _ w

theorem stationaryGenerator_resolvent (w : MassSpace) :
    stationaryGenerator ⟨stationaryResolvent w, ⟨w, rfl⟩⟩ = w - stationaryResolvent w :=
  generatorOfResolvent_apply _ _ w

theorem arithmeticGenerator_form (w : MassSpace) (q : SourceGraph) :
    ⟪arithmeticGenerator ⟨resolvent w, ⟨w, rfl⟩⟩, sourceMap q⟫_ℝ =
      ⟪(rieszLift w).val.snd, q.val.snd⟫_ℝ := by
  have h := inner_rieszLift w q
  rw [graph_inner] at h
  rw [arithmeticGenerator_resolvent, inner_sub_left]
  change ⟪w, q.val.fst⟫_ℝ - ⟪(rieszLift w).val.fst, q.val.fst⟫_ℝ = _
  linarith

theorem stationaryGenerator_form (w : MassSpace) (q : stationaryGroundGraph) :
    ⟪stationaryGenerator ⟨stationaryResolvent w, ⟨w, rfl⟩⟩, stationaryGroundSourceMap q⟫_ℝ =
      ⟪(stationaryRieszLift w).val.snd, q.val.snd⟫_ℝ := by
  have h := inner_stationaryRieszLift w q
  rw [Submodule.coe_inner, WithLp.prod_inner_apply] at h
  rw [stationaryGenerator_resolvent, inner_sub_left]
  change ⟪w, q.val.fst⟫_ℝ - ⟪(stationaryRieszLift w).val.fst, q.val.fst⟫_ℝ = _
  change ⟪(stationaryRieszLift w).val.fst, q.val.fst⟫_ℝ +
    ⟪(stationaryRieszLift w).val.snd, q.val.snd⟫_ℝ = ⟪w, q.val.fst⟫_ℝ at h
  linarith

theorem arithmeticGenerator_nonneg (u : arithmeticGenerator.domain) :
    0 ≤ ⟪arithmeticGenerator u, (u : MassSpace)⟫_ℝ := by
  rcases u with ⟨u, hu⟩
  obtain ⟨w, rfl⟩ := hu
  have h := arithmeticGenerator_form w (rieszLift w)
  change ⟪arithmeticGenerator ⟨resolvent w, _⟩, resolvent w⟫_ℝ = _ at h
  erw [h, real_inner_self_eq_norm_sq]
  positivity

theorem stationaryGenerator_nonneg (u : stationaryGenerator.domain) :
    0 ≤ ⟪stationaryGenerator u, (u : MassSpace)⟫_ℝ := by
  rcases u with ⟨u, hu⟩
  obtain ⟨w, rfl⟩ := hu
  have h := stationaryGenerator_form w (stationaryRieszLift w)
  change ⟪stationaryGenerator ⟨stationaryResolvent w, _⟩, stationaryResolvent w⟫_ℝ = _ at h
  erw [h, real_inner_self_eq_norm_sq]
  positivity

theorem arithmeticGenerator_domain_eq_stationary :
    arithmeticGenerator.domain = stationaryGenerator.domain := by
  apply SetLike.coe_injective
  exact full_operator_domain_eq_stationary

/-- Equality of the actual operators, on their common maximal domain. -/
theorem arithmeticGenerator_eq_stationary_add (u : arithmeticGenerator.domain) :
    arithmeticGenerator u = stationaryGenerator
      ⟨(u : MassSpace), arithmeticGenerator_domain_eq_stationary ▸ u.property⟩ +
        groundPerturbation u := by
  have hf := generatorOfResolvent_identity resolvent resolvent_injective u
  have hs := (full_generator_relation_iff_stationary (u : MassSpace) (arithmeticGenerator u)).mp hf
  have ht := generatorOfResolvent_identity stationaryResolvent stationaryResolvent_injective
    ⟨(u : MassSpace), arithmeticGenerator_domain_eq_stationary ▸ u.property⟩
  have heq := stationaryResolvent_injective (hs.trans ht.symm)
  rw [add_sub_assoc] at heq
  exact sub_eq_iff_eq_add.mp (add_left_cancel heq)

end RHTower.CHMDDoobGraph
