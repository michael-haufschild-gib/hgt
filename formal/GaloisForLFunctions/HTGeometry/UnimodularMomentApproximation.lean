import GaloisForLFunctions.HTGeometry.UnimodularRounding

/-!
# Rounding a moment solution to unimodular coefficients

Bagchi's rounding lemma, applied to the vector space of `J`-tuples of moments, converts a solution
of the interpolation system with coefficients in the closed unit disc into a solution with
coefficients on the unit *circle*, at a cost of at most `J` times the largest moment vector.

This is Andersson's Lemma 5 in coordinate-free form: the system is only approximately solved after
rounding, but the loss is `J` times the size of a single node's moment vector — negligible against
the target when the window carries many nodes.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- **Unimodular moment approximation.**  Rounding a unit-disc solution of a `J`-fold moment system
costs at most `J` times the largest node moment. -/
theorem exists_unimodular_moment_approx {N J : ℕ} (v : Fin N → Fin J → ℂ)
    (a : Fin N → ℂ) (ha : ∀ r, ‖a r‖ ≤ 1) {C : ℝ} (hC : ∀ r j, ‖v r j‖ ≤ C) (hC0 : 0 ≤ C) :
    ∃ b : Fin N → ℂ, (∀ r, ‖b r‖ = 1) ∧
      ∀ j : Fin J, ‖(∑ r, b r * v r j) - ∑ r, a r * v r j‖ ≤ (J : ℝ) * C := by
  classical
  have hnorm : ∀ r : Fin N, ‖v r‖ ≤ C := by
    intro r
    rcases Nat.eq_zero_or_pos J with hJ | hJ
    · subst hJ
      have hv0 : v r = 0 := Subsingleton.elim _ _
      rw [hv0, norm_zero]
      exact hC0
    · have : Nonempty (Fin J) := ⟨⟨0, hJ⟩⟩
      exact (pi_norm_le_iff_of_nonneg hC0).2 fun j => hC r j
  obtain ⟨b, hb1, hb2⟩ := exists_unimodular_rounding (E := Fin J → ℂ) v a ha hnorm hC0
  refine ⟨b, hb1, fun j => ?_⟩
  have hrank : Module.finrank ℂ (Fin J → ℂ) = J := by
    simp
  rw [hrank] at hb2
  have hsmul : ∀ (c : Fin N → ℂ) (j : Fin J),
      (∑ r, c r • v r) j = ∑ r, c r * v r j := by
    intro c j
    rw [Finset.sum_apply]
    exact Finset.sum_congr rfl fun r _ => rfl
  have hcoord : ‖(∑ r, b r • v r) j - (∑ r, a r • v r) j‖
      ≤ ‖(∑ r, b r • v r) - ∑ r, a r • v r‖ := by
    have := norm_le_pi_norm ((∑ r, b r • v r) - ∑ r, a r • v r) j
    simpa using this
  rw [hsmul b j, hsmul a j] at hcoord
  exact le_trans hcoord hb2

end GaloisForLFunctions.HTGeometry

end
