import GaloisForLFunctions.RepresentationLifting.Actions.DiscreteSL2
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Smooth actions over connected normed fields

Smoothness makes each individual orbit map locally constant. Connected
root subgroups therefore act trivially, with no dimension restriction on
the coefficient module. Elementary generation then gives determinant
descent for GL₂ over every connected nontrivially normed field.
Smoothness means that each vector is fixed on some identity neighborhood.
-/

noncomputable section
open Filter Topology Matrix
namespace GaloisForLFunctions.RepresentationLifting.ConnectedActions
variable {G k V : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Field k] [AddCommGroup V] [Module k V]

/-- Smoothness at the identity makes every orbit map locally constant everywhere. -/
theorem orbit_locallyConstant (ρ : G →* (V ≃ₗ[k] V))
    (hρ : ∀ v : V, ∀ᶠ g in 𝓝 (1 : G), ρ g v = v) (v : V) :
    IsLocallyConstant (fun g : G => ρ g v) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro g
  have hc : Tendsto (fun h : G => g⁻¹ * h) (𝓝 g) (𝓝 1) := by
    have hf : Continuous (fun h : G => g⁻¹ * h) := continuous_const.mul continuous_id
    simpa only [inv_mul_cancel] using (hf.continuousAt (x := g)).tendsto
  filter_upwards [hc.eventually (hρ v)] with h hh
  have he := congrArg (ρ g) hh
  change (ρ g * ρ (g⁻¹ * h)) v = ρ g v at he
  rw [← map_mul, mul_inv_cancel_left] at he
  exact he

/-- A continuous family through the identity in a connected parameter space acts trivially. -/
theorem connected_family_trivial {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    (ρ : G →* (V ≃ₗ[k] V))
    (hρ : ∀ v : V, ∀ᶠ g in 𝓝 (1 : G), ρ g v = v)
    (f : X → G) (hf : Continuous f) (x₀ : X) (h₀ : f x₀ = 1) (x : X) :
    ρ (f x) = 1 := by
  apply LinearEquiv.ext
  intro v
  change ρ (f x) v = v
  have hl := (orbit_locallyConstant ρ hρ v).comp_continuous hf
  have he := hl.apply_eq_of_preconnectedSpace x x₀
  exact he.trans (show ρ (f x₀) v = v by rw [h₀, map_one]; rfl)

variable {K : Type*} [NontriviallyNormedField K] [PreconnectedSpace K]
open GaloisForLFunctions.HTGeometry.LoopEisenstein

/-- Every smooth SL₂ action over a connected normed field is trivial in arbitrary dimension. -/
theorem smooth_sl2_trivial
    (ρ : SpecialLinearGroup (Fin 2) K →* (V ≃ₗ[k] V))
    (hρ : ∀ v : V, ∀ᶠ g in 𝓝 (1 : SpecialLinearGroup (Fin 2) K), ρ g v = v)
    (g : SpecialLinearGroup (Fin 2) K) : ρ g = 1 := by
  have hu (t : K) : ρ (sl2Upper t) = 1 :=
    connected_family_trivial ρ hρ sl2Upper DiscreteSL2.continuous_upper 0 sl2Upper_zero t
  have hl (t : K) : ρ (sl2Lower t) = 1 :=
    connected_family_trivial ρ hρ sl2Lower DiscreteSL2.continuous_lower 0 sl2Lower_zero t
  obtain ⟨x, y, z, w, h⟩ := HTGeometry.exists_elementary_factorization g.val g.property
  have hg : g = sl2Upper x * sl2Lower y * sl2Upper z * sl2Lower w := Subtype.ext h
  rw [hg]
  simp only [map_mul, hu, hl, mul_one]

/-- Every smooth GL₂ action over a connected normed field descends uniquely to determinant. -/
theorem smooth_det_factor
    (ρ : GeneralLinearGroup (Fin 2) K →* (V ≃ₗ[k] V))
    (hρ : ∀ v : V, ∀ᶠ g in 𝓝 (1 : GeneralLinearGroup (Fin 2) K), ρ g v = v) :
    ∃! χ : Kˣ →* (V ≃ₗ[k] V), χ.comp GeneralLinearGroup.det = ρ := by
  let d : GeneralLinearGroup (Fin 2) K →* Kˣ := GeneralLinearGroup.det
  have hk : d.ker ≤ ρ.ker := by
    intro g hg
    have hg' : g ∈ Set.range (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin 2) K → _) := by
      rw [SpecialLinearGroup.range_toGL]
      exact hg
    obtain ⟨s, rfl⟩ := hg'
    change ρ (SpecialLinearGroup.toGL s) = 1
    apply smooth_sl2_trivial (ρ.comp SpecialLinearGroup.toGL) ?_ s
    intro v
    have hc : ContinuousAt (SpecialLinearGroup.toGL :
        SpecialLinearGroup (Fin 2) K → GeneralLinearGroup (Fin 2) K) 1 :=
      SpecialLinearGroup.continuous_toGL.continuousAt
    have ht := hc.tendsto
    rw [map_one] at ht
    exact ht.eventually (hρ v)
  let e : {g : GeneralLinearGroup (Fin 2) K →* (V ≃ₗ[k] V) // d.ker ≤ g.ker} ≃
      (Kˣ →* (V ≃ₗ[k] V)) := d.liftOfSurjective GeneralLinearGroup.det_surjective
  refine ⟨e ⟨ρ, hk⟩, ?_, ?_⟩
  · exact congrArg Subtype.val (e.symm_apply_apply ⟨ρ, hk⟩)
  · intro χ hχ
    apply e.symm.injective
    apply Subtype.ext
    exact hχ.trans (congrArg Subtype.val (e.symm_apply_apply ⟨ρ, hk⟩)).symm

#print axioms orbit_locallyConstant
#print axioms connected_family_trivial
#print axioms smooth_sl2_trivial
#print axioms smooth_det_factor
end GaloisForLFunctions.RepresentationLifting.ConnectedActions
