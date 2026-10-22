import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerHasseResolvent
import Mathlib.Topology.Algebra.Module.LinearPMap

/-! # The graph closure of the original Meyer generator

The closed operator is obtained from the genuine source inverse. Its maximal
domain retains the full Jordan expression. The original cohomology is a
graph core, not only a dense subspace of the Hilbert carrier.
-/

noncomputable section
open Complex Set Topology

namespace RHTower

local notation "H" => DeningerArithmeticJetHilbert

def deningerMeyerHasseGraphDefect : (H × H) →L[ℂ] H :=
  ContinuousLinearMap.fst ℂ H H -
    deningerMeyerHasseResolvent.comp (ContinuousLinearMap.snd ℂ H H)

private theorem hasseGraph_singleValued (p : H × H)
    (hp : p ∈ deningerMeyerHasseGraphDefect.ker) (hx : p.1 = 0) : p.2 = 0 := by
  apply deningerMeyerHasseResolvent_injective
  change p.1 - deningerMeyerHasseResolvent p.2 = 0 at hp
  rw [hx, zero_sub] at hp
  simpa only [map_zero] using neg_eq_zero.mp hp

/-- Closed full-Jordan realization of the original centered Meyer generator. -/
def deningerMeyerClosedHasseGenerator : H →ₗ.[ℂ] H :=
  deningerMeyerHasseGraphDefect.ker.toLinearPMap

theorem deningerMeyerClosedHasseGenerator_graph :
    deningerMeyerClosedHasseGenerator.graph = deningerMeyerHasseGraphDefect.ker :=
  Submodule.toLinearPMap_graph_eq _ hasseGraph_singleValued

theorem mem_deningerMeyerClosedHasseGenerator_graph (x y : H) :
    (x, y) ∈ deningerMeyerClosedHasseGenerator.graph ↔ deningerMeyerHasseResolvent y = x := by
  rw [deningerMeyerClosedHasseGenerator_graph]
  change x - deningerMeyerHasseResolvent y = 0 ↔ deningerMeyerHasseResolvent y = x
  exact sub_eq_zero.trans eq_comm

theorem deningerMeyerClosedHasseGenerator_isClosed : deningerMeyerClosedHasseGenerator.IsClosed := by
  rw [LinearPMap.IsClosed, deningerMeyerClosedHasseGenerator_graph]
  exact deningerMeyerHasseGraphDefect.isClosed_ker

theorem deningerMeyerClosedHasseGenerator_domain :
    (deningerMeyerClosedHasseGenerator.domain : Set H) = range deningerMeyerHasseResolvent := by
  ext x
  change x ∈ deningerMeyerClosedHasseGenerator.domain ↔ _
  simp only [LinearPMap.mem_domain_iff, mem_deningerMeyerClosedHasseGenerator_graph, mem_range]

theorem deningerMeyerClosedHasseGenerator_dense :
    Dense (deningerMeyerClosedHasseGenerator.domain : Set H) := by
  rw [deningerMeyerClosedHasseGenerator_domain]
  exact deningerMeyerHasseResolvent_dense

theorem deningerMeyerHasseResolvent_of_equation (x y : H)
    (h : ∀ q, xiSpectralPoint q * x q - I * deningerHasseHilbertShift x q = y q) :
    deningerMeyerHasseResolvent y = x := by
  have he : deningerHasseResolventFactor x = deningerHasseDiagonalInverse y := by
    apply lp.ext
    funext q
    change x q - I * ((xiSpectralPoint q)⁻¹ * deningerHasseHilbertShift x q) =
      (xiSpectralPoint q)⁻¹ * y q
    rw [← h q]
    field_simp [xiSpectralPoint_ne_zero q]
  change Ring.inverse deningerHasseResolventFactor (deningerHasseDiagonalInverse y) = x
  rw [← he]
  exact congrArg (fun T : H →L[ℂ] H => T x)
    (Ring.inverse_mul_cancel _ deningerHasseResolventFactor_isUnit)

/-- Exact maximal domain; no boundary condition or semisimplification is added. -/
theorem mem_deningerMeyerClosedHasseGenerator_domain (x : H) :
    x ∈ deningerMeyerClosedHasseGenerator.domain ↔
      Memℓp (fun q => xiSpectralPoint q * x q - I * deningerHasseHilbertShift x q) 2 := by
  rw [LinearPMap.mem_domain_iff]
  constructor
  · rintro ⟨y, hy⟩
    have he := (mem_deningerMeyerClosedHasseGenerator_graph x y).mp hy
    have hf : (fun q => xiSpectralPoint q * x q - I * deningerHasseHilbertShift x q) =
        fun q => y q := by
      funext q
      rw [← he]
      exact deningerMeyerHasseResolvent_equation y q
    rw [hf]
    exact lp.memℓp y
  · intro hx
    let y : H := ⟨_, hx⟩
    exact ⟨y, (mem_deningerMeyerClosedHasseGenerator_graph x y).mpr
      (deningerMeyerHasseResolvent_of_equation x y (fun _ => rfl))⟩

theorem deningerMeyerClosedHasseGenerator_apply
    (x : deningerMeyerClosedHasseGenerator.domain) (q : DeningerArithmeticJetCoordinate) :
    deningerMeyerClosedHasseGenerator x q = xiSpectralPoint q * (x : H) q -
      I * deningerHasseHilbertShift (x : H) q := by
  have he := (mem_deningerMeyerClosedHasseGenerator_graph _ _).mp
    (deningerMeyerClosedHasseGenerator.mem_graph x)
  rw [← he]
  exact (deningerMeyerHasseResolvent_equation _ q).symm

/-- The literal source generator's graph in its faithful Hilbert realization. -/
def deningerMeyerHasseSourceGraph : Set (H × H) :=
  range fun u : DeningerMeyerStrongLogCohomology =>
    (deningerMeyerHasseHilbertLM u,
      deningerMeyerHasseHilbertLM (deningerMeyerCenteredGenerator u))

theorem deningerMeyerHasseSourceGraph_subset :
    deningerMeyerHasseSourceGraph ⊆ (deningerMeyerClosedHasseGenerator.graph : Set (H × H)) := by
  rintro _ ⟨u, rfl⟩
  exact (mem_deningerMeyerClosedHasseGenerator_graph _ _).mpr
    (deningerMeyerHasseResolvent_source_left u)

/-- **Source core theorem.** This closed operator is precisely the closure of
the original source generator, including all infinite source classes. -/
theorem deningerMeyerHasseSourceGraph_closure :
    closure deningerMeyerHasseSourceGraph =
      (deningerMeyerClosedHasseGenerator.graph : Set (H × H)) := by
  apply Subset.antisymm
  · exact closure_minimal deningerMeyerHasseSourceGraph_subset deningerMeyerClosedHasseGenerator_isClosed
  · rintro ⟨x, y⟩ hxy
    have he := (mem_deningerMeyerClosedHasseGenerator_graph x y).mp hxy
    rw [← he]
    let f : H → H × H := fun z => (deningerMeyerHasseResolvent z, z)
    have hf : Continuous f := deningerMeyerHasseResolvent.continuous.prodMk continuous_id
    have hi : f '' range deningerMeyerHasseHilbertLM ⊆ deningerMeyerHasseSourceGraph := by
      rintro _ ⟨_, ⟨u, rfl⟩, rfl⟩
      refine ⟨deningerMeyerCenteredGeneratorEquiv.symm u, ?_⟩
      apply Prod.ext
      · exact (deningerMeyerHasseResolvent_source u).symm
      · exact congrArg deningerMeyerHasseHilbertLM
          (deningerMeyerCenteredGeneratorEquiv.apply_symm_apply u)
    apply closure_mono hi
    exact image_closure_subset_closure_image hf
      ⟨y, deningerMeyerHasseHilbertLM_dense y, rfl⟩

end RHTower
