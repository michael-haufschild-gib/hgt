import GaloisForLFunctions.HTGeometry.GermCoordinateChange

/-!
# A linear change of coordinates as an isomorphism of germ rings

A linear automorphism of a finite-dimensional complex space is analytic together with its inverse
and fixes the origin, so it induces a ring isomorphism of the local rings of analytic germs at the
origin.  Combined with the regularization of a nonzero germ this is what lets an induction on the
dimension always assume that the germ under study is regular in the distinguished coordinate.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

variable {n : ℕ}

theorem analyticAt_linearMap (L : (Fin (n + 1) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))
    (p : Fin (n + 1) → ℂ) : AnalyticAt ℂ (fun w => L w) p :=
  (LinearMap.toContinuousLinearMap L).analyticAt p

/-- **A linear automorphism induces a ring isomorphism of the germ rings at the origin.** -/
noncomputable def germLinearEquiv (L : (Fin (n + 1) → ℂ) ≃ₗ[ℂ] (Fin (n + 1) → ℂ)) :
    AnalyticGerm (0 : Fin (n + 1) → ℂ) ≃+* AnalyticGerm (0 : Fin (n + 1) → ℂ) :=
  analyticGermEquiv (Φ := fun w => L w) (Ψ := fun w => L.symm w)
    (analyticAt_linearMap (L : (Fin (n + 1) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) 0)
    (analyticAt_linearMap (L.symm : (Fin (n + 1) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) 0)
    (map_zero L) (map_zero L.symm)
    (Filter.Eventually.of_forall fun w => L.symm_apply_apply w)
    (Filter.Eventually.of_forall fun w => L.apply_symm_apply w)

theorem germLinearEquiv_analyticGermOf (L : (Fin (n + 1) → ℂ) ≃ₗ[ℂ] (Fin (n + 1) → ℂ))
    {f : (Fin (n + 1) → ℂ) → ℂ} (hf : AnalyticAt ℂ f (0 : Fin (n + 1) → ℂ)) :
    (germLinearEquiv L (analyticGermOf hf) : Germ (𝓝 (0 : Fin (n + 1) → ℂ)) ℂ)
      = ((f ∘ fun w : Fin (n + 1) → ℂ => L w) : (Fin (n + 1) → ℂ) → ℂ) :=
  analyticGermPullback_analyticGermOf
    (analyticAt_linearMap (L : (Fin (n + 1) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) 0) (map_zero L) hf

/-- **Every nonzero germ becomes regular in the distinguished coordinate after applying a suitable
isomorphism of the germ ring.** -/
theorem exists_germLinearEquiv_regular {f : (Fin (n + 1) → ℂ) → ℂ}
    (hf : AnalyticAt ℂ f (0 : Fin (n + 1) → ℂ)) (hne : ¬ f =ᶠ[𝓝 (0 : Fin (n + 1) → ℂ)] 0) :
    ∃ (L : (Fin (n + 1) → ℂ) ≃ₗ[ℂ] (Fin (n + 1) → ℂ))
      (g : (Fin (n + 1) → ℂ) → ℂ) (hg : AnalyticAt ℂ g (0 : Fin (n + 1) → ℂ)),
      germLinearEquiv L (analyticGermOf hf) = analyticGermOf hg ∧
        ¬ (fun z : ℂ => g (Fin.cons z (0 : Fin n → ℂ))) =ᶠ[𝓝 (0 : ℂ)] 0 := by
  obtain ⟨L, hL⟩ := exists_regular_coordinate_change hf hne
  have hL0 : L (0 : Fin (n + 1) → ℂ) = 0 := map_zero L
  have hgA : AnalyticAt ℂ (fun w : Fin (n + 1) → ℂ => f (L w)) (0 : Fin (n + 1) → ℂ) := by
    have hfL : AnalyticAt ℂ f (L (0 : Fin (n + 1) → ℂ)) := by
      rw [hL0]
      exact hf
    exact hfL.comp (analyticAt_linearMap (L : (Fin (n + 1) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) 0)
  refine ⟨L, fun w => f (L w), hgA, ?_, hL⟩
  refine Subtype.ext ?_
  rw [germLinearEquiv_analyticGermOf L hf]
  rfl

end GaloisForLFunctions.HTGeometry
