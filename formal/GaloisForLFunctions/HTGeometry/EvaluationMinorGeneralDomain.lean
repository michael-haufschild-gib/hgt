import GaloisForLFunctions.HTGeometry.PrimeValuationProfileRankLaw

/-!
# Nonsingular evaluation minors over an arbitrary domain

A linearly independent family of scalar functions can always be separated by finitely many sample
points: there are points at which the evaluation matrix is nonsingular.

The corpus records this for sequences indexed by the naturals.  The argument never uses anything
about the index type, so it is restated here for an arbitrary domain.  That generality is what the
multi-row rank condition of the freeness predicate needs, where the samples are complex nodes rather
than natural coordinates.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Nonsingular evaluation minor, general domain.**  A finite linearly independent family of
scalar functions on any domain admits pairwise distinct sample points whose evaluation matrix is
nonsingular. -/
theorem exists_injective_evaluation_minor_of_linearIndependent
    {α : Type*} {d : ℕ} (u : Fin d → α → ℂ) (hu : LinearIndependent ℂ u) :
    ∃ (e : Fin d → α) (P : Matrix (Fin d) (Fin d) ℂ),
      Function.Injective e ∧ IsUnit P.det ∧
      ∀ r s, P r s = u s (e r) := by
  have hspan : Submodule.span ℂ (Set.range (flip u)) = ⊤ :=
    (span_flip_eq_top_iff_linearIndependent).2 hu
  obtain ⟨v, hvrange, _hvspan, hvLI⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq ℂ (Set.range (flip u))
  have hfinrank : Module.finrank ℂ
      (Submodule.span ℂ (Set.range (flip u))) = d := by
    rw [hspan]
    simp [Module.finrank_fintype_fun_eq_card]
  let E : Fin d ≃ Fin (Module.finrank ℂ
      (Submodule.span ℂ (Set.range (flip u)))) :=
    finCongr hfinrank.symm
  let w : Fin d → (Fin d → ℂ) := v ∘ E
  have hwrange : ∀ i, w i ∈ Set.range (flip u) := fun i => hvrange (E i)
  have hwLI : LinearIndependent ℂ w := hvLI.comp E E.injective
  choose e heval using hwrange
  have he : Function.Injective e := by
    intro i j hij
    apply hwLI.injective
    rw [← heval i, ← heval j, hij]
  let P : Matrix (Fin d) (Fin d) ℂ := Matrix.of fun r s => w r s
  have hProws : LinearIndependent ℂ P.row := by
    simpa only [P, Matrix.row, Matrix.of_apply] using hwLI
  obtain ⟨Q, hPQ⟩ := exists_matrix_rightInverse_of_linearIndependent_rows P hProws
  have hPdet : P.det ≠ 0 := Matrix.det_ne_zero_of_right_inverse hPQ
  refine ⟨e, P, he, isUnit_iff_ne_zero.mpr hPdet, ?_⟩
  intro r s
  change w r s = u s (e r)
  exact (congrFun (heval r) s).symm

end

end GaloisForLFunctions.HTGeometry
