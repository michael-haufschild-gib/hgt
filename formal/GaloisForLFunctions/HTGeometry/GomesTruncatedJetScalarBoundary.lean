import GaloisForLFunctions.HTGeometry.GomesTruncatedJetOrderAlgebra

/-!
# Sharp finite-horizon boundary for surviving geometric-clock symmetries

A nonconstant joint symmetry survives exactly when the actual phase has a
positive order smaller than the finite coefficient dimension. This includes
nonperiodic, zero, unit and arbitrarily high-order phases in one classification.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.GammaFactorialFock

/-- The phase-order generator is scalar exactly at order zero or beyond the finite horizon. -/
theorem gomesTruncatedJetClock_orderPower_scalar_iff (n : ℕ) (z : ℂ) :
    fockShiftMatrix (n + 1) ^ orderOf z ∈
        (⊥ : Subalgebra ℂ (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) ↔
      orderOf z = 0 ∨ n + 1 ≤ orderOf z := by
  constructor
  · intro h
    by_cases hd : orderOf z = 0
    · exact Or.inl hd
    · apply Or.inr
      by_contra hn
      have hlt : orderOf z < n + 1 := Nat.lt_of_not_ge hn
      obtain ⟨c, hc⟩ := (Algebra.mem_bot.mp h)
      have he : gomesFiniteFockFormalHom (n + 1) ((PowerSeries.X : PowerSeries ℂ) ^ orderOf z) =
          gomesFiniteFockFormalHom (n + 1) (PowerSeries.C c) := by
        rw [map_pow, gomesFiniteFockFormalHom_X, PowerSeries.C_eq_algebraMap,
          (gomesFiniteFockFormalHom (n + 1)).commutes]
        exact hc.symm
      have hk := (gomesFiniteFockFormalHom_eq_iff (n + 1) _ _).mp he ⟨orderOf z, hlt⟩
      simp only [PowerSeries.coeff_X_pow_self, PowerSeries.coeff_C, if_neg hd] at hk
      exact one_ne_zero hk
  · rintro (hd | hn)
    · rw [hd, pow_zero]
      exact (⊥ : Subalgebra ℂ (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)).one_mem
    · rw [pow_eq_zero_of_le hn (fockShiftMatrix_nilpotent (n + 1))]
      exact (⊥ : Subalgebra ℂ (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)).zero_mem

/-- The full joint symmetry algebra is scalar exactly at the sharp phase-order horizon boundary. -/
theorem gomesTruncatedJetJointAlgebra_eq_bot_iff (n : ℕ) (z : ℂ) :
    gomesTruncatedJetJointAlgebra n z = ⊥ ↔ orderOf z = 0 ∨ n + 1 ≤ orderOf z := by
  constructor
  · intro h
    apply (gomesTruncatedJetClock_orderPower_scalar_iff n z).mp
    rw [← h]
    exact gomesTruncatedJetJointAlgebra_orderPower_mem n z
  · intro h
    rw [gomesTruncatedJetJointAlgebra_eq_adjoin_orderPower]
    apply le_antisymm
    · exact Algebra.adjoin_singleton_le ((gomesTruncatedJetClock_orderPower_scalar_iff n z).mpr h)
    · exact bot_le

/-- A non-scalar joint symmetry exists precisely when a positive phase order fits below the horizon. -/
theorem gomesTruncatedJetJointAlgebra_exists_nonscalar_iff (n : ℕ) (z : ℂ) :
    (∃ M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
      M ∈ gomesTruncatedJetJointAlgebra n z ∧
        M ∉ (⊥ : Subalgebra ℂ (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))) ↔
      0 < orderOf z ∧ orderOf z < n + 1 := by
  constructor
  · rintro ⟨M, hM, hnot⟩
    have hb : ¬ (orderOf z = 0 ∨ n + 1 ≤ orderOf z) := by
      intro h
      exact hnot ((gomesTruncatedJetJointAlgebra_eq_bot_iff n z).mpr h ▸ hM)
    exact ⟨Nat.pos_of_ne_zero (fun h => hb (Or.inl h)),
      Nat.lt_of_not_ge (fun h => hb (Or.inr h))⟩
  · rintro ⟨hpos, hlt⟩
    refine ⟨fockShiftMatrix (n + 1) ^ orderOf z,
      gomesTruncatedJetJointAlgebra_orderPower_mem n z, ?_⟩
    intro h
    rcases (gomesTruncatedJetClock_orderPower_scalar_iff n z).mp h with hz | hh
    · exact (Nat.ne_of_gt hpos) hz
    · exact (Nat.not_le_of_gt hlt) hh

end GaloisForLFunctions.HTGeometry.GammaFactorialFock
