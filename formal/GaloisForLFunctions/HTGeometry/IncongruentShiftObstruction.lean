import GaloisForLFunctions.HTGeometry.SignedShiftOrbitMass

/-!
# The shift obstruction for pairwise incongruent shifts

This is the form the archimedean cards use.  When the shifts are pairwise incongruent modulo `ℤ`,
every unit orbit carries exactly one of them, so the orbit mass is a *single* weight, and the signed
obstruction applies as soon as that weight is nonzero.

Its intended use: the ratio of two Gamma monomials satisfies `R(z+1) = ρ(z) R(z)` with
`ρ(z) = ∏_k (z+λ_k)^{n_k}` rational, and the second logarithmic derivative of `ρ` is
`-∑_k n_k (z+λ_k)^{-2}`.  A rational solution of that shift equation is exactly what a linear
relation among Gamma monomials would produce, and this theorem forbids it.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

noncomputable section

/-- **The shift obstruction at pairwise incongruent shifts.**  A single nonzero weight suffices. -/
theorem not_shiftDifference_signedInvSq_of_incongruent {r : ℕ} (lam : Fin r → ℂ) (n : Fin r → ℂ)
    (hincong : ∀ k k' : Fin r, k ≠ k' → ∀ m : ℤ, lam k - lam k' ≠ (m : ℂ))
    (k₀ : Fin r) (hn : n k₀ ≠ 0)
    {y : ℂ → ℂ} (hy : MeromorphicOn y Set.univ)
    (hpoles : {z : ℂ | ¬ AnalyticAt ℂ y z}.Finite) :
    ¬ ((fun z => y (z + 1) - y z)
        =ᶠ[Filter.cofinite] fun z => ∑ k, n k * ((z + lam k) ^ (2 : ℕ))⁻¹) := by
  classical
  intro heq
  have hrw : (fun z : ℂ => ∑ k, n k * ((z + lam k) ^ (2 : ℕ))⁻¹)
      = fun z : ℂ => ∑ k ∈ (Finset.univ : Finset (Fin r)), n k * ((z - (-lam k)) ^ (2 : ℕ))⁻¹ := by
    funext z
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [sub_neg_eq_add]
  rw [hrw] at heq
  refine not_shiftDifference_weightedSumInvSq_orbit (H := 1) (a := -lam k₀) one_ne_zero
    (Finset.univ : Finset (Fin r)) n (fun k => -lam k) {k₀} (Finset.subset_univ _)
    (fun _ => 0) ?_ ?_ ?_ hy hpoles heq
  · intro i hi
    rw [Finset.mem_singleton] at hi
    subst hi
    simp
  · intro i _ hi m
    rw [Finset.mem_singleton] at hi
    intro hcon
    refine hincong k₀ i (fun h => hi h.symm) m ?_
    have : lam k₀ - lam i = (m : ℂ) := by linear_combination hcon
    exact this
  · rw [Finset.sum_singleton]
    exact hn

end

end GaloisForLFunctions.HTGeometry
