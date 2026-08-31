import GaloisForLFunctions.HTGeometry.AnchoredCesaroVarianceCompletion

/-!
# Scale innovation-history bundle

Every discrete scale potential reconstructs one unique anchored formation tail.  Its weighted
successor increment is the next history innovation, and the centered old history is orthogonal to
the uniform recentering component.  This turns the variance--Dirichlet identity into an inductive
rank-one history geometry and proves that every completed correction current creates a genuine
completed history rather than an external error term.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Unique formation tail reconstructed from a prescribed scale potential. -/
def scalePotentialInnovationHistory (P : ℕ → ℝ) (n : ℕ) : ℝ :=
  if n = 2 then P 2 else
    ((n + 1 : ℕ) : ℝ) * P n - (n : ℝ) * P (n - 1)

theorem scalePotentialInnovationHistory_two (P : ℕ → ℝ) :
    scalePotentialInnovationHistory P 2 = P 2 := by
  simp [scalePotentialInnovationHistory]

theorem scalePotentialInnovationHistory_succ
    (P : ℕ → ℝ) {N : ℕ} (hN : 2 ≤ N) :
    scalePotentialInnovationHistory P (N + 1) =
      ((N + 2 : ℕ) : ℝ) * P (N + 1) -
        ((N + 1 : ℕ) : ℝ) * P N := by
  rw [scalePotentialInnovationHistory, if_neg (by omega : N + 1 ≠ 2)]
  rw [Nat.add_sub_cancel]

/-- Reconstructed history has exactly the prescribed anchored potential. -/
theorem anchoredCesaroPotential_scalePotentialInnovationHistory
    (P : ℕ → ℝ) {N : ℕ} (hN : 2 ≤ N) :
    anchoredCesaroPotential (scalePotentialInnovationHistory P) N = P N := by
  induction N, hN using Nat.le_induction with
  | base =>
      rw [anchoredCesaroPotential_two,
        scalePotentialInnovationHistory_two]
  | succ N hN ih =>
      have hupdate := anchoredCesaroPotential_succ_sub
        (scalePotentialInnovationHistory P) hN
      rw [anchoredCesaroHighPass, ih,
        scalePotentialInnovationHistory_succ P hN] at hupdate
      have hden : ((N + 2 : ℕ) : ℝ) ≠ 0 := by positivity
      field_simp [hden] at hupdate
      push_cast at hupdate ⊢
      nlinarith

/-- Reconstructed-history innovation is the weighted potential increment. -/
theorem anchoredCesaroHighPass_scalePotentialInnovationHistory
    (P : ℕ → ℝ) {N : ℕ} (hN : 2 ≤ N) :
    anchoredCesaroHighPass (scalePotentialInnovationHistory P) N =
      ((N + 2 : ℕ) : ℝ) * (P (N + 1) - P N) := by
  rw [anchoredCesaroHighPass,
    scalePotentialInnovationHistory_succ P hN,
    anchoredCesaroPotential_scalePotentialInnovationHistory P hN]
  push_cast
  ring

/-- A prescribed scale potential determines its anchored history tail uniquely. -/
theorem scalePotentialInnovationHistory_unique
    (P a : ℕ → ℝ)
    (hpotential : ∀ N, 2 ≤ N → anchoredCesaroPotential a N = P N) :
    a 2 = scalePotentialInnovationHistory P 2 ∧
      ∀ N, 2 ≤ N → a (N + 1) = scalePotentialInnovationHistory P (N + 1) := by
  constructor
  · rw [scalePotentialInnovationHistory_two,
      ← hpotential 2 (by omega), anchoredCesaroPotential_two]
  · intro N hN
    have hterminal := anchoredCesaro_terminal_reconstruction a N
    have hcurrent := anchoredCesaroHighPass_eq_scaled_potentialIncrement a hN
    rw [hpotential N hN] at hterminal hcurrent
    rw [hpotential (N + 1) (by omega)] at hcurrent
    rw [scalePotentialInnovationHistory_succ P hN]
    push_cast at hterminal hcurrent ⊢
    nlinarith

/-- Centered anchored history has total weighted mass zero. -/
theorem anchoredCesaro_centeredMass_eq_zero
    (a : ℕ → ℝ) {N : ℕ} (hN : 2 ≤ N) :
    3 * (a 2 - anchoredCesaroPotential a N) +
        ∑ j ∈ Finset.Ico 3 (N + 1),
          (a j - anchoredCesaroPotential a N) = 0 := by
  have hcard : ((Finset.Ico 3 (N + 1)).card : ℝ) = (N : ℝ) - 2 := by
    rw [Nat.card_Ico, Nat.cast_sub (by omega : 3 ≤ N + 1)]
    push_cast
    ring
  have hmean : 3 * a 2 + ∑ j ∈ Finset.Ico 3 (N + 1), a j =
      (N + 1 : ℕ) * anchoredCesaroPotential a N := by
    unfold anchoredCesaroPotential
    have hden : ((N + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp [hden]
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hcard]
  push_cast at hmean ⊢
  linarith

/-- Old centered history is orthogonal to the uniform recentering innovation. -/
theorem anchoredCesaro_oldResidual_orthogonal_uniformInnovation
    (a : ℕ → ℝ) {N : ℕ} (hN : 2 ≤ N) :
    3 * (a 2 - anchoredCesaroPotential a N) *
          (-anchoredCesaroHighPass a N / (N + 2 : ℕ)) +
        ∑ j ∈ Finset.Ico 3 (N + 1),
          (a j - anchoredCesaroPotential a N) *
            (-anchoredCesaroHighPass a N / (N + 2 : ℕ)) = 0 := by
  have hcenter := anchoredCesaro_centeredMass_eq_zero a hN
  rw [← Finset.sum_mul]
  linear_combination
    (-anchoredCesaroHighPass a N / (N + 2 : ℕ)) * hcenter

/-- Every old residual receives the same successor recentering component. -/
theorem anchoredCesaro_oldResidual_succ
    (a : ℕ → ℝ) {N j : ℕ} (hN : 2 ≤ N) :
    a j - anchoredCesaroPotential a (N + 1) =
      (a j - anchoredCesaroPotential a N) -
        anchoredCesaroHighPass a N / (N + 2 : ℕ) := by
  have hupdate := anchoredCesaroPotential_succ_sub a hN
  linarith

/-- New terminal residual is the complementary rank-one innovation component. -/
theorem anchoredCesaro_newResidual_succ
    (a : ℕ → ℝ) {N : ℕ} (hN : 2 ≤ N) :
    a (N + 1) - anchoredCesaroPotential a (N + 1) =
      ((N + 1 : ℕ) : ℝ) / (N + 2 : ℕ) *
        anchoredCesaroHighPass a N := by
  have hupdate := anchoredCesaroPotential_succ_sub a hN
  have hterminal := anchoredCesaro_terminal_reconstruction a N
  have hden : ((N + 2 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp [hden] at hupdate ⊢
  push_cast at hupdate ⊢
  nlinarith

/-- Variance of the reconstructed history is exactly scale Dirichlet energy. -/
theorem scalePotentialInnovationHistory_variance_eq_dirichletEnergy
    (P : ℕ → ℝ) {N : ℕ} (hN : 2 ≤ N) :
    anchoredCesaroVariance (scalePotentialInnovationHistory P) N =
      scaleDirichletEnergy P N := by
  rw [anchoredCesaroVariance_eq_scaleDirichletEnergy _ hN]
  unfold scaleDirichletEnergy
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Finset.mem_Ico] at hk
  rw [anchoredCesaroPotential_scalePotentialInnovationHistory P hk.1,
    anchoredCesaroPotential_scalePotentialInnovationHistory P (by omega)]

/-- Reconstructed history of a potential completed by an arbitrary correction current. -/
def completedScaleInnovationHistory (a r : ℕ → ℝ) : ℕ → ℝ :=
  scalePotentialInnovationHistory (completedScalePotential a r)

/-- Completed history projects to the completed scale potential. -/
theorem anchoredCesaroPotential_completedScaleInnovationHistory
    (a r : ℕ → ℝ) {N : ℕ} (hN : 2 ≤ N) :
    anchoredCesaroPotential (completedScaleInnovationHistory a r) N =
      completedScalePotential a r N := by
  exact anchoredCesaroPotential_scalePotentialInnovationHistory _ hN

/-- Completed-history innovation is original current plus correction current. -/
theorem anchoredCesaroHighPass_completedScaleInnovationHistory
    (a r : ℕ → ℝ) {N : ℕ} (hN : 2 ≤ N) :
    anchoredCesaroHighPass (completedScaleInnovationHistory a r) N =
      anchoredCesaroHighPass a N + r N := by
  rw [completedScaleInnovationHistory,
    anchoredCesaroHighPass_scalePotentialInnovationHistory _ hN]
  exact completedScalePotential_scaled_succ_sub a r hN

/-- Completed source action is exactly variance of the completed innovation history. -/
theorem anchoredCesaroVariance_completedScaleInnovationHistory
    (a r : ℕ → ℝ) {N : ℕ} (hN : 2 ≤ N) :
    anchoredCesaroVariance (completedScaleInnovationHistory a r) N =
      completedScaleDirichletEnergy a r N := by
  exact scalePotentialInnovationHistory_variance_eq_dirichletEnergy _ hN

end

end GaloisForLFunctions.HTGeometry
