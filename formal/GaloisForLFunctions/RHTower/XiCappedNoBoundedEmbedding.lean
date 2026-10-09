import GaloisForLFunctions.RHTower.XiCappedAnalyticAtlas
import GaloisForLFunctions.HTGeometry.ParabolicOpenEmbedding
import GaloisForLFunctions.RHTower.ArithmeticJointJetExclusion
import Mathlib.Analysis.Complex.Liouville

open Topology Set Function
open scoped UpperHalfPlane Manifold ContDiff

namespace RHTower.XiMarkedMonodromy
open GaloisForLFunctions.HTGeometry

/-- An actual capped Xi factorization cannot admit an injective bounded analytic coordinate. -/
theorem not_exists_bounded_injective_analytic_map_of_cappedXiLift
    (H : Subgroup (coveringDeckGroup markedUniversalCover))
    (G : C(ℂ, CappedMarkedCover H))
    (hG : ∀ z, cappedMarkedProjection H (G z) = xi z) :
    ¬ ∃ u : CappedMarkedCover H → ℂ,
      ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω u ∧ Injective u ∧ Bornology.IsBounded (range u) := by
  rintro ⟨u, hu, hinj, hb⟩
  have hc : Differentiable ℂ (u ∘ G) :=
    (hu.comp (contMDiff_cappedXiLift H G hG)).contDiff.differentiable (by simp)
  have hbc : Bornology.IsBounded (range (u ∘ G)) :=
    hb.subset (range_comp_subset_range _ _)
  obtain ⟨t, _, _, hz, _⟩ := DeletionMixedRefinement.exists_high_simple_critical_xi 0
  have he := hinj (hc.apply_eq_apply_of_bounded hbc (DeletionMixedRefinement.criticalResponsePoint t) 0)
  have hξ := congrArg (cappedMarkedProjection H) he
  rw [hG, hG, hz, xi_zero] at hξ
  norm_num at hξ

/-- The actual analytic factor surface is simply connected and admits no bounded analytic embedding. -/
theorem xi_capped_factorization_no_bounded_analytic_embedding :
    ∃ H : Subgroup (coveringDeckGroup markedUniversalCover),
      SimplyConnectedSpace (CappedMarkedCover H) ∧
      (¬ ∃ u : CappedMarkedCover H → ℂ,
        ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω u ∧ Injective u ∧ Bornology.IsBounded (range u)) ∧
      ∃ G : C(ℂ, CappedMarkedCover H),
        ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω G ∧
        ∀ z, cappedMarkedProjection H (G z) = xi z := by
  obtain ⟨H, hs, _, G, hGa, hG⟩ := xi_analytic_simplyConnected_capped_factorization
  exact ⟨H, hs, not_exists_bounded_injective_analytic_map_of_cappedXiLift H G hG, G, hGa, hG⟩

/-- For the actual factor surface, any analytic open embedding into the plane is already onto.
This theorem does not assume or assert that such an embedding exists. -/
theorem xi_capped_factorization_planar_embeddings_surjective :
    ∃ H : Subgroup (coveringDeckGroup markedUniversalCover),
      SimplyConnectedSpace (CappedMarkedCover H) ∧
      (∀ u : CappedMarkedCover H → ℂ,
        ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω u → IsOpenEmbedding u → Surjective u) ∧
      ∃ G : C(ℂ, CappedMarkedCover H),
        ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω G ∧
        ∀ z, cappedMarkedProjection H (G z) = xi z := by
  obtain ⟨H, hs, hnb, G, hGa, hG⟩ := xi_capped_factorization_no_bounded_analytic_embedding
  letI := hs
  exact ⟨H, hs, fun _ hu he => surjective_analytic_openEmbedding_of_no_bounded_embedding hnb hu he,
    G, hGa, hG⟩

end RHTower.XiMarkedMonodromy
