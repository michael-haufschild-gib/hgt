import GaloisForLFunctions.HTGeometry.EllipticFundamentalPoles
import GaloisForLFunctions.HTGeometry.MeromorphicLaurentLeading

/-!
# Poles with an invariant principal part lie on finitely many lattice cosets

A point is a pole exactly when some Laurent coefficient of negative index is nonzero — one direction
is the corpus's `meromorphicOrderAt_neg_of_laurentCoeff_ne_zero`, the other is the leading-coefficient
law.  So a function whose negative Laurent coefficients are invariant under two `ℝ`-independent
translations has a translation-invariant pole set, and since a meromorphic function has finitely many
poles in the compact fundamental parallelogram, its poles lie on finitely many cosets of the lattice.

For a mixed-constraint source this is what bounds the bookkeeping: the boundary function `Δ_τ F` has
`σ`-lattice-invariant principal parts, so the `σ`-lines carrying poles of `F` are finite in number,
and symmetrically for the `τ`-lines.

* `meromorphicOrderAt_neg_iff_exists_laurentCoeff_ne_zero`;
* `exists_finset_pole_classes`.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex

/-- **A pole is exactly a nonzero negative Laurent coefficient.** -/
theorem meromorphicOrderAt_neg_iff_exists_laurentCoeff_ne_zero {U : ℂ → ℂ} {z : ℂ}
    (hU : MeromorphicAt U z) :
    meromorphicOrderAt U z < 0 ↔ ∃ ℓ : ℤ, ℓ < 0 ∧ laurentCoeff U z ℓ ≠ 0 := by
  constructor
  · intro hlt
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    exact absurd (meromorphicOrderAt_nonneg_of_laurentCoeff_neg_eq_zero hU hcon) (not_le.mpr hlt)
  · rintro ⟨ℓ, hℓ, hne⟩
    exact meromorphicOrderAt_neg_of_laurentCoeff_ne_zero hU hℓ hne

/-- **Poles with a translation-invariant pole set lie on finitely many lattice cosets.** -/
theorem exists_finset_pole_classes {U : ℂ → ℂ} {w₁ w₂ : ℂ}
    (hU : MeromorphicOn U Set.univ) (hindep : LinearIndependent ℝ ![w₁, w₂])
    (hinv : ∀ (m n : ℤ) (z : ℂ), meromorphicOrderAt U z < 0 →
      meromorphicOrderAt U (z - (m • w₁ + n • w₂)) < 0) :
    ∃ P : Finset ℂ, ∀ z : ℂ, meromorphicOrderAt U z < 0 →
      ∃ m n : ℤ, z - (m • w₁ + n • w₂) ∈ P := by
  classical
  refine ⟨(finite_poles_fundamentalParallelogram hU w₁ w₂).toFinset, fun z hz => ?_⟩
  obtain ⟨C, _, hcov⟩ := exists_bounded_intCombination hindep
  obtain ⟨m, n, hmem, _, _⟩ := hcov z
  refine ⟨m, n, ?_⟩
  rw [Set.Finite.mem_toFinset]
  exact ⟨hmem, hinv m n z hz⟩

/-- The pole set is invariant when the negative Laurent coefficients are. -/
theorem pole_invariant_of_laurentCoeff_invariant {U : ℂ → ℂ} {w : ℂ}
    (hU : MeromorphicOn U Set.univ)
    (hinv : ∀ (ℓ : ℤ), ℓ < 0 → ∀ z : ℂ, laurentCoeff U (z + w) ℓ = laurentCoeff U z ℓ)
    {z : ℂ} (hz : meromorphicOrderAt U z < 0) :
    meromorphicOrderAt U (z + w) < 0 := by
  obtain ⟨ℓ, hℓ, hne⟩ :=
    (meromorphicOrderAt_neg_iff_exists_laurentCoeff_ne_zero (hU z (Set.mem_univ z))).mp hz
  refine (meromorphicOrderAt_neg_iff_exists_laurentCoeff_ne_zero
    (hU (z + w) (Set.mem_univ _))).mpr ⟨ℓ, hℓ, ?_⟩
  rw [hinv ℓ hℓ z]
  exact hne

end GaloisForLFunctions.HTGeometry
