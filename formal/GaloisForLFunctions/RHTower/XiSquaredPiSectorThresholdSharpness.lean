import GaloisForLFunctions.RHTower.XiSquaredCompleteMonotonicityPiFarRay

open Complex

namespace RHTower

noncomputable section

/-- The `pi` threshold is sharp for any proof using only the closed critical-strip width.
Below threshold, the boundary coordinates `b=1/2`, `gamma=(n+1)/pi` have positive longitudinal
part but violate the exact angle budget. -/
theorem exists_xiPiSector_closedStripWitness_of_lt_threshold
    {n : ℕ} (hn : 1 ≤ n) {X : ℝ} (hX0 : 0 ≤ X)
    (hX : X < xiSquaredPiFarRayThreshold n) :
    ∃ gamma b : ℝ,
      0 < gamma ∧ |b| ≤ 1 / 2 ∧ 0 < gamma ^ 2 - b ^ 2 + X ∧
        (Real.pi / (2 * ((n : ℝ) + 1))) *
            (gamma ^ 2 - b ^ 2 + X) < |2 * gamma * b| := by
  let m : ℝ := (n : ℝ) + 1
  let gamma : ℝ := m / Real.pi
  let b : ℝ := 1 / 2
  let t : ℝ := Real.pi / (2 * m)
  have hm : 0 < m := by dsimp [m]; positivity
  have hm2 : 2 ≤ m := by
    dsimp [m]
    exact_mod_cast Nat.add_le_add_right hn 1
  have hgamma : 0 < gamma := by dsimp [gamma]; positivity
  have hgammaHalf : 1 / 2 < gamma := by
    dsimp [gamma]
    rw [lt_div_iff₀ Real.pi_pos]
    nlinarith [Real.pi_lt_four]
  have hlong : 0 < gamma ^ 2 - b ^ 2 + X := by
    dsimp [b]
    nlinarith [sq_nonneg (gamma - 1 / 2)]
  have hcore : gamma ^ 2 - b ^ 2 + X < 2 * gamma ^ 2 := by
    unfold xiSquaredPiFarRayThreshold at hX
    have hgammaSq : gamma ^ 2 = m ^ 2 / Real.pi ^ 2 := by
      dsimp [gamma]
      field_simp [Real.pi_ne_zero]
    dsimp [b]
    rw [hgammaSq]
    nlinarith
  have ht : 0 < t := by dsimp [t]; positivity
  have hscaled : t * (gamma ^ 2 - b ^ 2 + X) < t * (2 * gamma ^ 2) :=
    mul_lt_mul_of_pos_left hcore ht
  have hright : t * (2 * gamma ^ 2) = gamma := by
    dsimp [t, gamma]
    field_simp [Real.pi_ne_zero, ne_of_gt hm]
  have habs : |2 * gamma * b| = gamma := by
    dsimp [b]
    rw [show 2 * gamma * (1 / 2) = gamma by ring, abs_of_pos hgamma]
  refine ⟨gamma, b, hgamma, ?_, hlong, ?_⟩
  · dsimp [b]
    norm_num
  · change t * (gamma ^ 2 - b ^ 2 + X) < |2 * gamma * b|
    exact hscaled.trans_eq (hright.trans habs.symm)

end

end RHTower
