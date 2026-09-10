import GaloisForLFunctions.HTGeometry.GomesTruncatedJetOrderAlgebra

/-!
# Complete comparison of the symmetries supplied by two geometric phases

Finite joint symmetry algebras remember exactly which integer weights resonate
below the jet horizon. Inclusion and equality of the full matrix algebras are
therefore classified by inclusion and equality of these finite weight sets.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.GammaFactorialFock

/-- Below the horizon, an actual clock power is a joint symmetry exactly at a resonant weight. -/
theorem gomesTruncatedJetJointAlgebra_clockPower_mem_iff (n : ℕ) (z : ℂ)
    (k : Fin (n + 1)) :
    fockShiftMatrix (n + 1) ^ k.val ∈ gomesTruncatedJetJointAlgebra n z ↔ orderOf z ∣ k.val := by
  rw [gomesTruncatedJetJointAlgebra_mem_iff,
    and_iff_right ((Commute.refl (fockShiftMatrix (n + 1))).pow_left k.val)]
  rw [← gomesFiniteFockFormalHom_X, ← map_pow, gomesTruncatedJetClock_formal_commute_iff_order]
  constructor
  · intro h
    have hk := h k
    rw [PowerSeries.coeff_X_pow_self] at hk
    exact hk.resolve_left one_ne_zero
  · intro hk j
    rw [PowerSeries.coeff_X_pow]
    by_cases hj : j.val = k.val
    · exact Or.inr (hj ▸ hk)
    · exact Or.inl (if_neg hj)

/-- Inclusion of full joint symmetry algebras is exactly inclusion of their finite resonant weight sets. -/
theorem gomesTruncatedJetJointAlgebra_le_iff_weights (n : ℕ) (z w : ℂ) :
    gomesTruncatedJetJointAlgebra n z ≤ gomesTruncatedJetJointAlgebra n w ↔
      ∀ k : Fin (n + 1), orderOf z ∣ k.val → orderOf w ∣ k.val := by
  constructor
  · intro h k hk
    exact (gomesTruncatedJetJointAlgebra_clockPower_mem_iff n w k).mp
      (h ((gomesTruncatedJetJointAlgebra_clockPower_mem_iff n z k).mpr hk))
  · intro h M hM
    obtain ⟨c, ⟨hc, hr⟩, _⟩ := (gomesTruncatedJetJointAlgebra_unique_symbol n z M).mp hM
    apply (gomesTruncatedJetJointAlgebra_mem_iff n w M).mpr
    constructor
    · exact ((gomesTruncatedJetJointAlgebra_mem_iff n z M).mp hM).1
    · rw [← hc]
      apply (gomesTruncatedJetClock_polynomial_commute_iff n w _).mpr
      intro k
      rw [gomesFiniteFockCoefficientPolynomial_coeff]
      exact (hr k).imp_right (h k)

/-- Two actual geometric phases supply exactly the same full matrix symmetries iff their finite resonances coincide. -/
theorem gomesTruncatedJetJointAlgebra_eq_iff_weights (n : ℕ) (z w : ℂ) :
    gomesTruncatedJetJointAlgebra n z = gomesTruncatedJetJointAlgebra n w ↔
      ∀ k : Fin (n + 1), orderOf z ∣ k.val ↔ orderOf w ∣ k.val := by
  constructor
  · intro h k
    exact ⟨(gomesTruncatedJetJointAlgebra_le_iff_weights n z w).mp h.le k,
      (gomesTruncatedJetJointAlgebra_le_iff_weights n w z).mp h.ge k⟩
  · intro h
    apply le_antisymm
    · exact (gomesTruncatedJetJointAlgebra_le_iff_weights n z w).mpr (fun k => (h k).mp)
    · exact (gomesTruncatedJetJointAlgebra_le_iff_weights n w z).mpr (fun k => (h k).mpr)

end GaloisForLFunctions.HTGeometry.GammaFactorialFock
