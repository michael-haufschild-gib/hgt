import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.FiniteCompletionFibres

/-! Finite places contract with finite fibres. An eventual condition on
the upstairs places consequently holds on every fibre outside a finite set. -/

noncomputable section

open NumberField IsDedekindDomain Filter

namespace GlobalTheory.Reciprocity

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem finitePlace_under_eq_iff (w : HeightOneSpectrum (𝓞 L))
    (v : HeightOneSpectrum (𝓞 K)) :
    w.under (𝓞 K) = v ↔ w.asIdeal.LiesOver v.asIdeal := by
  constructor
  · rintro rfl
    exact ⟨rfl⟩
  · intro h
    exact HeightOneSpectrum.ext h.over.symm

theorem tendsto_finitePlace_under :
    Tendsto (HeightOneSpectrum.under (𝓞 K) : HeightOneSpectrum (𝓞 L) → _) cofinite cofinite := by
  apply Filter.Tendsto.cofinite_of_finite_preimage_singleton
  intro v
  refine ((finitePlacesAbove L v).finite_toSet.subset ?_).to_subtype
  intro w hw
  exact (mem_finitePlacesAbove L v w).mpr ((finitePlace_under_eq_iff w v).mp hw)

theorem eventually_forall_finitePlacesAbove {P : HeightOneSpectrum (𝓞 L) → Prop}
    (h : ∀ᶠ w in cofinite, P w) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 K) in cofinite, ∀ w : finitePlacesAbove L v, P w.val := by
  rw [eventually_cofinite] at h ⊢
  refine (h.image (HeightOneSpectrum.under (𝓞 K))).subset fun v hv => ?_
  simp only [Set.mem_setOf_eq, not_forall] at hv
  obtain ⟨w, hw⟩ := hv
  exact ⟨w.val, hw, (finitePlace_under_eq_iff w.val v).mpr inferInstance⟩

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.eventually_forall_finitePlacesAbove
