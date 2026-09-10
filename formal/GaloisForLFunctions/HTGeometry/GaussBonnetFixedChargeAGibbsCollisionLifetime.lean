import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsBinomialInformationHistory

/-!
# A probability law for the temporal collision tail

Normalizing accumulated positive-time collision excess measures when the
remaining distinguishability is present. A nonzero tail is a probability law;
an input erased after one step has the identically zero tail instead.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- Total positive-time collision mass. -/
def egbFixedChargeAGibbsCollisionTailMass (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) : ℝ :=
  (4 / 5 : ℝ) * egbFixedChargeAGibbsSlowModeEnergy n β E +
    (1 / 35 : ℝ) * egbFixedChargeAGibbsFastModeEnergy n β E

/-- Collision mass at time `m + 1`, normalized by the entire positive-time tail. -/
def egbFixedChargeAGibbsCollisionTailHistory (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) (m : ℕ) : ℝ :=
  egbFixedChargeAGibbsCollisionExcess n (m + 1) β E / egbFixedChargeAGibbsCollisionTailMass n β E

/-- Exact mean positive time for the normalized collision history. -/
def egbFixedChargeAGibbsCollisionMeanTime (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) : ℝ :=
  ((36 / 25 : ℝ) * egbFixedChargeAGibbsSlowModeEnergy n β E +
    (36 / 1225 : ℝ) * egbFixedChargeAGibbsFastModeEnergy n β E) /
      egbFixedChargeAGibbsCollisionTailMass n β E

private theorem tail_mass_nonneg (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) : 0 ≤ egbFixedChargeAGibbsCollisionTailMass n β E := by
  have hA := egbFixedChargeAGibbsSlowModeEnergy_nonneg n β E
  have hB := egbFixedChargeAGibbsFastModeEnergy_nonneg n β E
  unfold egbFixedChargeAGibbsCollisionTailMass
  positivity

/-- The temporal collision mass vanishes exactly when both surviving Fourier energies vanish. -/
theorem egbFixedChargeAGibbsCollisionTailMass_zero_iff (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeAGibbsCollisionTailMass n β E = 0 ↔
      egbFixedChargeAGibbsSlowModeEnergy n β E = 0 ∧ egbFixedChargeAGibbsFastModeEnergy n β E = 0 := by
  have hA := egbFixedChargeAGibbsSlowModeEnergy_nonneg n β E
  have hB := egbFixedChargeAGibbsFastModeEnergy_nonneg n β E
  unfold egbFixedChargeAGibbsCollisionTailMass
  constructor
  · intro h; constructor <;> nlinarith
  · rintro ⟨ha, hb⟩; rw [ha, hb]; ring

/-- Every normalized temporal collision weight is nonnegative. -/
theorem egbFixedChargeAGibbsCollisionTailHistory_nonneg (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) : 0 ≤ egbFixedChargeAGibbsCollisionTailHistory n β E m :=
  div_nonneg (egbFixedChargeAGibbsCollisionExcess_nonneg n (m + 1) β E) (tail_mass_nonneg n β E)

/-- Every surviving input gives a normalized time distribution; an erased input gives zero total mass. -/
theorem egbFixedChargeAGibbsCollisionTailHistory_mass (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    HasSum (egbFixedChargeAGibbsCollisionTailHistory n β E)
      (if egbFixedChargeAGibbsSlowModeEnergy n β E = 0 ∧
        egbFixedChargeAGibbsFastModeEnergy n β E = 0 then 0 else 1) := by
  change HasSum (fun m : ℕ => egbFixedChargeAGibbsCollisionExcess n (m + 1) β E /
    egbFixedChargeAGibbsCollisionTailMass n β E)
      (if egbFixedChargeAGibbsSlowModeEnergy n β E = 0 ∧
        egbFixedChargeAGibbsFastModeEnergy n β E = 0 then 0 else 1)
  have h : HasSum (fun m : ℕ => egbFixedChargeAGibbsCollisionExcess n (m + 1) β E)
      (egbFixedChargeAGibbsCollisionTailMass n β E) :=
    egbFixedChargeAGibbsCollisionExcess_two_rate_tail_hasSum n β E
  have hs := h.div_const (egbFixedChargeAGibbsCollisionTailMass n β E)
  by_cases hz : egbFixedChargeAGibbsSlowModeEnergy n β E = 0 ∧
      egbFixedChargeAGibbsFastModeEnergy n β E = 0
  · have ht := (egbFixedChargeAGibbsCollisionTailMass_zero_iff n β E).mpr hz
    simpa only [egbFixedChargeAGibbsCollisionTailHistory, if_pos hz, ht, div_zero] using hs
  · have ht : egbFixedChargeAGibbsCollisionTailMass n β E ≠ 0 :=
      fun h => hz ((egbFixedChargeAGibbsCollisionTailMass_zero_iff n β E).mp h)
    simpa only [egbFixedChargeAGibbsCollisionTailHistory, if_neg hz, div_self ht] using hs

/-- The explicit mean time is the actual first moment of the normalized collision history. -/
theorem egbFixedChargeAGibbsCollisionTailHistory_mean_hasSum (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    HasSum (fun m : ℕ => ((m : ℝ) + 1) * egbFixedChargeAGibbsCollisionTailHistory n β E m)
      (egbFixedChargeAGibbsCollisionMeanTime n β E) := by
  have h := egbFixedChargeAGibbsCollisionExcess_binomial_hasSum n 1 β E
  norm_num [egbFixedChargeAGibbsBinomialCollisionBudget] at h
  have hs := h.div_const (egbFixedChargeAGibbsCollisionTailMass n β E)
  have he : (fun m : ℕ => ((m : ℝ) + 1) * egbFixedChargeAGibbsCollisionTailHistory n β E m) =
      (fun m : ℕ => (((m : ℝ) + 1) * egbFixedChargeAGibbsCollisionExcess n (m + 1) β E) /
        egbFixedChargeAGibbsCollisionTailMass n β E) := by
    funext m; unfold egbFixedChargeAGibbsCollisionTailHistory; ring
  rw [he]
  exact hs

end
end GaloisForLFunctions.HTGeometry
