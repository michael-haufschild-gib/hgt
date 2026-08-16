import GaloisForLFunctions.HTGeometry.LatticeFundamentalCover
import GaloisForLFunctions.HTGeometry.SiegelClearedCombination

/-!
# Translating into the cover, and periodicity of a combination

The two halves of the transition data a chartwise Siegel argument needs.

Geometrically: for a subgroup with compact quotient and any prescribed radius there is a *finite*
set of centres such that every point of the space is congruent, modulo the subgroup, to a point
within that radius of one of them.  This is the finite cover of a fundamental set, restated as a
statement about arbitrary points.

Algebraically: a combination of periodic functions is periodic, because the combination depends on
the functions only through their values at the point.  Together these say that the value of the
combination of the quotients at any point equals its value at a point of some small polydisc — which
is what makes the chart comparison constant finite.
-/

namespace GaloisForLFunctions.HTGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Every point translates into the cover.**  For a subgroup with compact quotient there is a
finite set of centres such that every point is congruent to a point within `r` of one of them. -/
theorem exists_period_centre_of_compactSpace_quotient {P : AddSubgroup E}
    (h : CompactSpace (E ⧸ P)) {r : ℝ} (hr : 0 < r) :
    ∃ s : Set E, s.Finite ∧ s.Nonempty ∧
      ∀ z : E, ∃ p ∈ P, ∃ c ∈ s, ‖z - p - c‖ ≤ r := by
  obtain ⟨K, s, hKcomp, hKne, hfund, hsfin, hcov⟩ :=
    exists_finite_centres_of_compactSpace_quotient h hr
  have hsne : s.Nonempty := by
    obtain ⟨z, hz⟩ := hKne
    obtain ⟨c, hc, -⟩ := hcov z hz
    exact ⟨c, hc⟩
  refine ⟨s, hsfin, hsne, ?_⟩
  intro z
  obtain ⟨p, hp, hzp⟩ := hfund z
  obtain ⟨c, hc, hzc⟩ := hcov _ hzp
  exact ⟨p, hp, c, hc, hzc⟩

/-! ## Periodicity of a combination -/

variable {n m : ℕ}

/-- **A combination of periodic functions is periodic.** -/
theorem siegelCombination_periodic {F : Type*} [AddGroup F] (f : Fin (n + 1) → F → ℂ)
    (a : (Fin (n + 1) → Fin (m + 1)) → ℂ) {p : F}
    (hper : ∀ k w, f k (w + p) = f k w) (w : F) :
    siegelCombination f a (w + p) = siegelCombination f a w := by
  simp only [siegelCombination]
  refine Finset.sum_congr rfl fun β _ => ?_
  congr 1
  exact Finset.prod_congr rfl fun k _ => by rw [hper k w]

/-- **A cleared combination of periodic data is periodic.** -/
theorem siegelHomCombination_periodic {F : Type*} [AddGroup F] (A B : Fin (n + 1) → F → ℂ)
    (a : (Fin (n + 1) → Fin (m + 1)) → ℂ) {p : F}
    (hA : ∀ k w, A k (w + p) = A k w) (hB : ∀ k w, B k (w + p) = B k w) (w : F) :
    siegelHomCombination A B m a (w + p) = siegelHomCombination A B m a w := by
  simp only [siegelHomCombination]
  refine Finset.sum_congr rfl fun β _ => ?_
  congr 1
  exact Finset.prod_congr rfl fun k _ => by rw [hA k w, hB k w]

end GaloisForLFunctions.HTGeometry
