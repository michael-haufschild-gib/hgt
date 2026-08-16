import GaloisForLFunctions.HTGeometry.GermReducedFraction

/-!
# Factoriality at every point

Translation is an analytic change of coordinates, so the ring of analytic germs at any point is
isomorphic to the ring at the origin.  Factoriality therefore holds at every point of `ℂ^n`, not
only at the origin, and with it the reduced-fraction theory: a meromorphic germ has a reduced
presentation at each of the finitely many centres of a cover, unique up to units.

That is what a chartwise Siegel argument needs, since its centres are the points of a cover of a
fundamental parallelotope and there is no reason for any of them to be the origin.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem analyticAt_sub_const (p : E) (w : E) :
    AnalyticAt ℂ (fun z : E => z - p) w := by
  have h := (analyticAt_id (𝕜 := ℂ) (z := w)).sub (analyticAt_const (v := p))
  rw [Pi.sub_def] at h
  exact h

theorem analyticAt_add_const (p : E) (w : E) :
    AnalyticAt ℂ (fun z : E => z + p) w := by
  have h := (analyticAt_id (𝕜 := ℂ) (z := w)).add (analyticAt_const (v := p))
  rw [Pi.add_def] at h
  exact h

/-- **Translation is an isomorphism of germ rings.** -/
noncomputable def germTranslate (p : E) : AnalyticGerm (0 : E) ≃+* AnalyticGerm p :=
  analyticGermEquiv (Φ := fun z : E => z - p) (Ψ := fun z : E => z + p)
    (analyticAt_sub_const p p) (analyticAt_add_const p 0)
    (by simp) (by simp)
    (Filter.Eventually.of_forall fun w => by simp)
    (Filter.Eventually.of_forall fun w => by simp)

/-- **Factoriality at every point of `ℂ^n`.** -/
theorem uniqueFactorizationMonoid_analyticGerm {n : ℕ} (p : Fin n → ℂ) :
    UniqueFactorizationMonoid (AnalyticGerm p) := by
  classical
  refine UniqueFactorizationMonoid.of_exists_prime_factors ?_
  intro a ha
  set e := germTranslate p with he
  have ha' : e.symm a ≠ 0 := by
    intro h
    refine ha ?_
    have := congrArg e h
    rwa [RingEquiv.apply_symm_apply, map_zero] at this
  obtain ⟨f, hfp, hfassoc⟩ :=
    UniqueFactorizationMonoid.exists_prime_factors (e.symm a) ha'
  refine ⟨f.map e, ?_, ?_⟩
  · intro b hb
    obtain ⟨c, hc, rfl⟩ := Multiset.mem_map.mp hb
    exact (MulEquiv.prime_iff (e : AnalyticGerm (0 : Fin n → ℂ) ≃* AnalyticGerm p)).mpr (hfp c hc)
  · obtain ⟨u, hu⟩ := hfassoc
    refine ⟨u.map (e : AnalyticGerm (0 : Fin n → ℂ) →* AnalyticGerm p), ?_⟩
    rw [← map_multiset_prod]
    have := congrArg e hu
    rw [map_mul, RingEquiv.apply_symm_apply] at this
    rw [← this]
    rfl

end GaloisForLFunctions.HTGeometry
