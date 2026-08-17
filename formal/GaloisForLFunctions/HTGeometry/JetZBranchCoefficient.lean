import GaloisForLFunctions.HTGeometry.JetEigenRigidity

/-!
# The linear coefficient of the sliced shift

Above jet level three the sliced shift is linear, and its coefficient satisfies

`R'^2·Φ(u) = R'·u − m·R''`.

Adding `m·z₂` turns this into the pure eigen-relation `R'·Φ(h) = h`, whose exponent is one; by
rigidity the only torus-invariant solution is zero, so the coefficient is *exactly* `−m·z₂` — with no
freedom and no case analysis, at every level.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

variable {C : Type*} [Field C] [CharZero C]

/-- **The linear coefficient is pinned.** -/
theorem eq_neg_mul_jetRatio_two_of_linear (R : RatFunc C) (hR : substitutionDeriv R ≠ 0)
    {K : ℕ} (hK : 2 ≤ K)
    (hfix : ∀ g : JetField C Unit, (∀ j : ℕ, K < j → JetField.pd ((), j) g = 0) →
      jetSubstitution R hR g = g → ∃ e : C, g = algebraMap C (JetField C Unit) e)
    {u : JetField C Unit} (hwz : IsWeightZero u)
    (hord : ∀ j : ℕ, K < j → JetField.pd ((), j) u = 0) {m : C}
    (heq : substitutionDeriv R ^ 2 * jetSubstitution R hR u
      = substitutionDeriv R * u
        - algebraMap C (JetField C Unit) m * JetField.pd ((), 0) (substitutionDeriv R)) :
    u = -(algebraMap C (JetField C Unit) m * (jetRatio 2 : JetField C Unit)) := by
  classical
  set ρ : JetField C Unit := substitutionDeriv R with hρdef
  have hρ0 : ρ ≠ 0 := hR
  set mJ : JetField C Unit := algebraMap C (JetField C Unit) m with hmdef
  set h : JetField C Unit := u + mJ * (jetRatio 2 : JetField C Unit) with hhdef
  -- the pure eigen-relation
  have hz2 : ρ ^ 2 * jetSubstitution R hR (jetRatio 2 : JetField C Unit)
      = ρ * (jetRatio 2 : JetField C Unit) + JetField.pd ((), 0) ρ := by
    have hj := jetSubstitution_jetRatio R hR 2
    rw [substitutionShiftRatio_two] at hj
    exact hj
  have heigen : ρ ^ (1 : ℤ) * jetSubstitution R hR h = h := by
    rw [zpow_one]
    refine mul_left_cancel₀ hρ0 ?_
    rw [hhdef, map_add, map_mul, AlgHom.commutes]
    linear_combination heq + mJ * hz2
  -- rigidity
  have hwzh : IsWeightZero h := by
    refine IsWeightZero.add hwz (IsWeightZero.mul ?_ (isWeightZero_jetRatio 2))
    rw [hmdef]
    exact isWeightZero_algebraMap m
  have hordh : ∀ j : ℕ, K < j → JetField.pd ((), j) h = 0 := by
    intro j hj
    have hleib := (JetField.pd ((), j) :
      Derivation C (JetField C Unit) (JetField C Unit)).leibniz mJ
        (jetRatio 2 : JetField C Unit)
    simp only [smul_eq_mul] at hleib
    rw [hhdef, map_add, hord j hj, hleib, hmdef, Derivation.map_algebraMap,
      pd_jetRatio_of_ne (by omega) (by omega)]
    ring
  have hh0 : h = 0 := by
    by_contra hne
    have := exponent_eq_zero_of_weightZero_eigen R hR (K := K) (by omega) hfix hwzh hne hordh
      heigen
    exact absurd this (by norm_num)
  rw [hhdef] at hh0
  linear_combination hh0

end

end GaloisForLFunctions.HTGeometry
