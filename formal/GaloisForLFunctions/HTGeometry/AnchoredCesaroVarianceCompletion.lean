import GaloisForLFunctions.HTGeometry.AnchoredCesaroScaleConnection

/-!
# Anchored Cesàro variance and completion primitive

The anchored Cesàro potential carries an exact positive action.  Its unnormalised variance is the
scale Dirichlet energy of the potential, and every additive correction current on the scale ray
has a canonical finite-sum primitive.  Consequently the square of the completed current is the
exact successor production of a monotone completed Dirichlet energy.
-/

open Filter
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Raw second moment for the anchored history, with the initial sample carrying weight three. -/
def anchoredCesaroSecondMoment (a : ℕ → ℝ) (N : ℕ) : ℝ :=
  3 * (a 2) ^ 2 + ∑ j ∈ Finset.Ico 3 (N + 1), (a j) ^ 2

/-- Unnormalised variance of the anchored formation history. -/
def anchoredCesaroVariance (a : ℕ → ℝ) (N : ℕ) : ℝ :=
  anchoredCesaroSecondMoment a N -
    (N + 1 : ℕ) * (anchoredCesaroPotential a N) ^ 2

theorem anchoredCesaroSecondMoment_succ
    (a : ℕ → ℝ) {N : ℕ} (hN : 2 ≤ N) :
    anchoredCesaroSecondMoment a (N + 1) =
      anchoredCesaroSecondMoment a N + (a (N + 1)) ^ 2 := by
  unfold anchoredCesaroSecondMoment
  rw [show N + 1 + 1 = (N + 1) + 1 by omega,
    Finset.sum_Ico_succ_top (by omega : 3 ≤ N + 1)]
  ring

/-- Online variance production: the new high-pass current contributes one positive square. -/
theorem anchoredCesaroVariance_succ_sub
    (a : ℕ → ℝ) {N : ℕ} (hN : 2 ≤ N) :
    anchoredCesaroVariance a (N + 1) - anchoredCesaroVariance a N =
      ((N + 1 : ℕ) : ℝ) / (N + 2 : ℕ) *
        (anchoredCesaroHighPass a N) ^ 2 := by
  rw [anchoredCesaroVariance, anchoredCesaroVariance,
    anchoredCesaroSecondMoment_succ a hN]
  have hm := anchoredCesaroPotential_succ_sub a hN
  have hx := anchoredCesaro_terminal_reconstruction a N
  have hm' : anchoredCesaroPotential a (N + 1) =
      anchoredCesaroPotential a N + anchoredCesaroHighPass a N / (N + 2 : ℕ) := by
    linarith
  rw [hm', hx]
  have hden : ((N + 2 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp [hden]
  push_cast
  ring

theorem anchoredCesaroVariance_two (a : ℕ → ℝ) :
    anchoredCesaroVariance a 2 = 0 := by
  rw [anchoredCesaroVariance, anchoredCesaroSecondMoment,
    anchoredCesaroPotential_two]
  norm_num

/-- The raw-moment variance is exactly the sum of centered squares. -/
theorem anchoredCesaroVariance_eq_centered
    (a : ℕ → ℝ) {N : ℕ} (hN : 2 ≤ N) :
    anchoredCesaroVariance a N =
      3 * (a 2 - anchoredCesaroPotential a N) ^ 2 +
        ∑ j ∈ Finset.Ico 3 (N + 1),
          (a j - anchoredCesaroPotential a N) ^ 2 := by
  let m := anchoredCesaroPotential a N
  have hmean : 3 * a 2 + ∑ j ∈ Finset.Ico 3 (N + 1), a j = (N + 1 : ℕ) * m := by
    dsimp only [m]
    unfold anchoredCesaroPotential
    have hden : ((N + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp [hden]
  have hcard : ((Finset.Ico 3 (N + 1)).card : ℝ) = (N : ℝ) - 2 := by
    rw [Nat.card_Ico, Nat.cast_sub (by omega : 3 ≤ N + 1)]
    push_cast
    ring
  have hsum :
      (∑ j ∈ Finset.Ico 3 (N + 1), (a j - m) ^ 2) =
        (∑ j ∈ Finset.Ico 3 (N + 1), (a j) ^ 2) -
          2 * m * (∑ j ∈ Finset.Ico 3 (N + 1), a j) +
          ((Finset.Ico 3 (N + 1)).card : ℝ) * m ^ 2 := by
    calc
      _ = ∑ j ∈ Finset.Ico 3 (N + 1),
          ((a j) ^ 2 - 2 * m * a j + m ^ 2) := by
            apply Finset.sum_congr rfl
            intro j hj
            ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          Finset.sum_const, nsmul_eq_mul]
        rw [← Finset.mul_sum]
  rw [anchoredCesaroVariance, anchoredCesaroSecondMoment, hsum]
  dsimp only [m] at hmean ⊢
  rw [hcard]
  push_cast at hmean ⊢
  linear_combination 2 * anchoredCesaroPotential a N * hmean

theorem anchoredCesaroVariance_nonneg
    (a : ℕ → ℝ) {N : ℕ} (hN : 2 ≤ N) :
    0 ≤ anchoredCesaroVariance a N := by
  rw [anchoredCesaroVariance_eq_centered a hN]
  positivity

/-- Anchored variance descends through the constant-gauge quotient. -/
theorem anchoredCesaroVariance_add_const
    (a : ℕ → ℝ) (c : ℝ) {N : ℕ} (hN : 2 ≤ N) :
    anchoredCesaroVariance (fun k => a k + c) N = anchoredCesaroVariance a N := by
  rw [anchoredCesaroVariance_eq_centered _ hN,
    anchoredCesaroVariance_eq_centered _ hN,
    anchoredCesaroPotential_add_const a c hN]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro j hj
    ring

/-- Weighted Dirichlet energy along the discrete scale ray. -/
def scaleDirichletEnergy (P : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.Ico 2 N,
    ((k + 1 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ) * (P (k + 1) - P k) ^ 2

theorem scaleDirichletEnergy_succ_sub
    (P : ℕ → ℝ) {N : ℕ} (hN : 2 ≤ N) :
    scaleDirichletEnergy P (N + 1) - scaleDirichletEnergy P N =
      ((N + 1 : ℕ) : ℝ) * ((N + 2 : ℕ) : ℝ) *
        (P (N + 1) - P N) ^ 2 := by
  unfold scaleDirichletEnergy
  rw [Finset.sum_Ico_succ_top hN]
  ring

/-- Variance--Dirichlet conservation for the anchored formation potential. -/
theorem anchoredCesaroVariance_eq_scaleDirichletEnergy
    (a : ℕ → ℝ) {N : ℕ} (hN : 2 ≤ N) :
    anchoredCesaroVariance a N =
      scaleDirichletEnergy (anchoredCesaroPotential a) N := by
  induction N, hN using Nat.le_induction with
  | base =>
      rw [anchoredCesaroVariance_two]
      unfold scaleDirichletEnergy
      norm_num
  | succ N hN ih =>
      have hv := anchoredCesaroVariance_succ_sub a hN
      have he := scaleDirichletEnergy_succ_sub (anchoredCesaroPotential a) hN
      have hh := anchoredCesaroHighPass_eq_scaled_potentialIncrement a hN
      rw [ih] at hv
      have hden : ((N + 2 : ℕ) : ℝ) ≠ 0 := by positivity
      rw [hh] at hv
      field_simp [hden] at hv
      push_cast at hv he ⊢
      nlinarith

/-- Canonical primitive of a correction current on the scale ray. -/
def scaleCurrentPrimitive (r : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.Ico 2 N, r k / (k + 2 : ℕ)

theorem scaleCurrentPrimitive_two (r : ℕ → ℝ) :
    scaleCurrentPrimitive r 2 = 0 := by
  unfold scaleCurrentPrimitive
  norm_num

/-- The scale primitive has the prescribed correction current as its weighted derivative. -/
theorem scaleCurrentPrimitive_succ_sub
    (r : ℕ → ℝ) {N : ℕ} (hN : 2 ≤ N) :
    scaleCurrentPrimitive r (N + 1) - scaleCurrentPrimitive r N =
      r N / (N + 2 : ℕ) := by
  unfold scaleCurrentPrimitive
  rw [Finset.sum_Ico_succ_top hN]
  ring

/-- Completed scale potential obtained by integrating the correction current. -/
def completedScalePotential (a r : ℕ → ℝ) (N : ℕ) : ℝ :=
  anchoredCesaroPotential a N + scaleCurrentPrimitive r N

/-- Exact lift: completed source current is a pure weighted connection increment. -/
theorem completedScalePotential_scaled_succ_sub
    (a r : ℕ → ℝ) {N : ℕ} (hN : 2 ≤ N) :
    (N + 2 : ℕ) *
        (completedScalePotential a r (N + 1) - completedScalePotential a r N) =
      anchoredCesaroHighPass a N + r N := by
  have hp := anchoredCesaroPotential_succ_sub a hN
  have hr := scaleCurrentPrimitive_succ_sub r hN
  have hp' : anchoredCesaroPotential a (N + 1) =
      anchoredCesaroPotential a N + anchoredCesaroHighPass a N / (N + 2 : ℕ) := by
    linarith
  have hr' : scaleCurrentPrimitive r (N + 1) =
      scaleCurrentPrimitive r N + r N / (N + 2 : ℕ) := by
    linarith
  rw [completedScalePotential, completedScalePotential, hp', hr']
  have hden : ((N + 2 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp [hden]
  ring

/-- Dirichlet energy of the completed scale potential. -/
def completedScaleDirichletEnergy (a r : ℕ → ℝ) (N : ℕ) : ℝ :=
  scaleDirichletEnergy (completedScalePotential a r) N

/-- Positive completed formation-action production. -/
theorem completedScaleDirichletEnergy_succ_sub
    (a r : ℕ → ℝ) {N : ℕ} (hN : 2 ≤ N) :
    completedScaleDirichletEnergy a r (N + 1) -
        completedScaleDirichletEnergy a r N =
      ((N + 1 : ℕ) : ℝ) / (N + 2 : ℕ) *
        (anchoredCesaroHighPass a N + r N) ^ 2 := by
  rw [completedScaleDirichletEnergy, completedScaleDirichletEnergy,
    scaleDirichletEnergy_succ_sub _ hN]
  have hcurrent := completedScalePotential_scaled_succ_sub a r hN
  have hden : ((N + 2 : ℕ) : ℝ) ≠ 0 := by positivity
  rw [← hcurrent]
  field_simp [hden]

/-- Completed formation action is monotone along the scale ray. -/
theorem completedScaleDirichletEnergy_monotoneOn
    (a r : ℕ → ℝ) {K N : ℕ} (hK : 2 ≤ K) (hKN : K ≤ N) :
    completedScaleDirichletEnergy a r K ≤ completedScaleDirichletEnergy a r N := by
  induction N, hKN using Nat.le_induction with
  | base => exact le_rfl
  | succ N hKN ih =>
      have hN : 2 ≤ N := hK.trans hKN
      have hinc := completedScaleDirichletEnergy_succ_sub a r hN
      have hcoef : (0 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) / (N + 2 : ℕ) := by positivity
      nlinarith [mul_nonneg hcoef (sq_nonneg (anchoredCesaroHighPass a N + r N))]

end

end GaloisForLFunctions.HTGeometry
