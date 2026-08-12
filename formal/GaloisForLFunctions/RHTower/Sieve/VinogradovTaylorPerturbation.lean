import GaloisForLFunctions.RHTower.Sieve.VinogradovUpperHalfSaving
import GaloisForLFunctions.RHTower.Sieve.DirichletLipschitz

namespace RHTower.Sieve

open scoped BigOperators

noncomputable section

def vinogradovUpperHalfPairPhase
    {Q k : ℕ} (α : Fin k → ℝ) (l m : Fin Q) : ℝ :=
  ∑ j : Fin k, α j *
    ((((Q + l.val) : ℝ) * ((Q + m.val) : ℝ)) ^ (j.val + 1))

def vinogradovUpperHalfPerturbedBilinearSum
    {Q k : ℕ} (α : Fin k → ℝ)
    (ε : Fin Q → Fin Q → ℝ) : ℂ :=
  ∑ l : Fin Q, ∑ m : Fin Q,
    finitePhaseChar (vinogradovUpperHalfPairPhase α l m + ε l m)

theorem finitePhaseChar_lipschitz (x y : ℝ) :
    ‖finitePhaseChar x - finitePhaseChar y‖ ≤ 2 * Real.pi * |x - y| := by
  unfold finitePhaseChar
  have h := norm_exp_phase_sub_le (2 * Real.pi * x) (2 * Real.pi * y)
  convert h using 1
  rw [show 2 * Real.pi * x - 2 * Real.pi * y =
    (2 * Real.pi) * (x - y) by ring, abs_mul]
  have hpi : 0 ≤ 2 * Real.pi := by positivity
  rw [abs_of_nonneg hpi]

theorem norm_vinogradovUpperHalfPerturbedBilinearSum_sub_le
    {Q k : ℕ} (α : Fin k → ℝ) (ε : Fin Q → Fin Q → ℝ) {η : ℝ}
    (hη : ∀ l m, |ε l m| ≤ η) :
    ‖vinogradovUpperHalfPerturbedBilinearSum α ε -
        vinogradovUpperHalfBilinearSum Q α‖ ≤
      2 * Real.pi * η * (Q : ℝ) ^ 2 := by
  rw [vinogradovUpperHalfBilinearSum_eq]
  unfold vinogradovUpperHalfPerturbedBilinearSum
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ l : Fin Q,
        ‖(∑ m : Fin Q,
            finitePhaseChar (vinogradovUpperHalfPairPhase α l m + ε l m)) -
          ∑ m : Fin Q, finitePhaseChar (vinogradovUpperHalfPairPhase α l m)‖ :=
      norm_sum_le _ _
    _ = ∑ l : Fin Q,
        ‖∑ m : Fin Q,
          (finitePhaseChar (vinogradovUpperHalfPairPhase α l m + ε l m) -
            finitePhaseChar (vinogradovUpperHalfPairPhase α l m))‖ := by
      apply Finset.sum_congr rfl
      intro l _
      rw [Finset.sum_sub_distrib]
    _ ≤ ∑ l : Fin Q, ∑ m : Fin Q,
        ‖finitePhaseChar (vinogradovUpperHalfPairPhase α l m + ε l m) -
          finitePhaseChar (vinogradovUpperHalfPairPhase α l m)‖ := by
      exact Finset.sum_le_sum fun l _ => norm_sum_le _ _
    _ ≤ ∑ _l : Fin Q, ∑ _m : Fin Q, 2 * Real.pi * η := by
      apply Finset.sum_le_sum
      intro l _
      apply Finset.sum_le_sum
      intro m _
      calc
        _ ≤ 2 * Real.pi *
            |(vinogradovUpperHalfPairPhase α l m + ε l m) -
              vinogradovUpperHalfPairPhase α l m| :=
          finitePhaseChar_lipschitz _ _
        _ ≤ 2 * Real.pi * η := by
          rw [add_sub_cancel_left]
          gcongr
          exact hη l m
    _ = 2 * Real.pi * η * (Q : ℝ) ^ 2 := by
      simp
      ring

/-- Quantitative Taylor-perturbation interface: a uniform phase error
adds exactly `2πηQ²` to the already-proved upper-half bilinear saving. -/
theorem norm_vinogradovUpperHalfPerturbedBilinearSum_le
    {u Q : ℕ} (hu : 141 ≤ u)
    (hQ : vinogradovRouteTMomentConstant u ≤ 2 * Q)
    (α : Fin (vinogradovRouteTOrder (4 * u)) → ℝ)
    (ε : Fin Q → Fin Q → ℝ) {η : ℝ}
    (hη : ∀ l m, |ε l m| ≤ η)
    (a q : Fin (vinogradovRouteTOrder (4 * u)) → ℕ)
    (hq : ∀ j, vinogradovUsefulCoordinate u j → 0 < q j)
    (hcop : ∀ j, vinogradovUsefulCoordinate u j →
      Nat.Coprime (a j) (q j))
    (happrox : ∀ j, vinogradovUsefulCoordinate u j →
      |α j - (a j : ℝ) / (q j : ℝ)| ≤ 1 / (q j : ℝ) ^ 2)
    (hRq : ∀ j, vinogradovUsefulCoordinate u j →
      (2 * Q) ^ (2 * vinogradovCoordinateSavingExponent j) ≤ q j)
    (hqR : ∀ j, vinogradovUsefulCoordinate u j →
      q j * (2 * Q) ^ (2 * vinogradovCoordinateSavingExponent j) ≤
        ((2 * Q) ^ (j.val + 1)) ^ 2)
    (habsorb : ∀ j, vinogradovUsefulCoordinate u j →
      32 * (vinogradovRouteTMoment (4 * u) : ℝ) ^ 2 *
          (1 + Real.log ((q j : ℝ) + 1)) ≤
        ((2 * Q : ℕ) : ℝ) ^ vinogradovCoordinateSavingExponent j) :
    ‖vinogradovUpperHalfPerturbedBilinearSum α ε‖ ≤
      ((2 * Q : ℕ) : ℝ) ^ (2 - vinogradovRouteTPowerSavingExponent u) +
        2 * Real.pi * η * (Q : ℝ) ^ 2 := by
  calc
    _ ≤ ‖vinogradovUpperHalfBilinearSum Q α‖ +
        ‖vinogradovUpperHalfPerturbedBilinearSum α ε -
          vinogradovUpperHalfBilinearSum Q α‖ :=
      norm_le_norm_add_norm_sub' _ _
    _ ≤ ((2 * Q : ℕ) : ℝ) ^
          (2 - vinogradovRouteTPowerSavingExponent u) +
        2 * Real.pi * η * (Q : ℝ) ^ 2 :=
      add_le_add
        (norm_vinogradovUpperHalfBilinearSum_le_rpow hu hQ α a q
          hq hcop happrox hRq hqR habsorb)
        (norm_vinogradovUpperHalfPerturbedBilinearSum_sub_le α ε hη)

end

end RHTower.Sieve
