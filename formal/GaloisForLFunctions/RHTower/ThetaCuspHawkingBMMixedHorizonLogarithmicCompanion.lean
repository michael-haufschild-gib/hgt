import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMMixedHorizonResonantTruncation

/-!
# Formal logarithmic companion at the resonant mixed BM horizon

For `c = -N`, let `u = X^(N+1) ₂F₁(a+N+1,b+N+1;N+2;X)`. Applying the Gauss operator to
`u log X` produces a non-logarithmic forcing. This module constructs the unique analytic formal
part with constant coefficient one and zero free `u` component which cancels that forcing.

Its infinite tail uses finite reciprocal sums

`r_k = sum_(s=1)^k (1/(a+N+s) + 1/(b+N+s) - 1/s - 1/(N+1+s))`.

These are the finite-increment form of the digamma combination in DLMF 15.10.8. The proof uses
only corpus Gauss recurrences and field algebra: the terminal truncation obstruction cancels at
degree `N+1`, and every later coefficient cancels by variation of constants.

`[BRIDGE] [PAPER-PROVED] [LEAN-PROVED] [NOVELTY UNVERIFIED]`
-/

open Complex Nat Polynomial

namespace RHTower

noncomputable section

/-- Coefficient of the shifted regular exponent-`N+1` Gauss factor. -/
def d4HypergeometricResonantRegularCoefficient (N : ℕ) (a b : ℂ) (k : ℕ) : ℂ :=
  ordinaryHypergeometricCoefficient
    (a + ((N + 1 : ℕ) : ℂ))
    (b + ((N + 1 : ℕ) : ℂ))
    (((N + 2 : ℕ) : ℂ)) k

/-- Finite reciprocal-sum multiplier for the analytic tail of the logarithmic companion. -/
def d4HypergeometricResonantLogTailMultiplier (N : ℕ) (a b : ℂ) (k : ℕ) : ℂ :=
  ∑ j ∈ Finset.range k,
    ((a + (N : ℂ) + ((j + 1 : ℕ) : ℂ))⁻¹ +
      (b + (N : ℂ) + ((j + 1 : ℕ) : ℂ))⁻¹ -
      (((j + 1 : ℕ) : ℂ))⁻¹ -
      (((N + j + 2 : ℕ) : ℂ))⁻¹)

@[simp] theorem d4HypergeometricResonantLogTailMultiplier_zero (N : ℕ) (a b : ℂ) : d4HypergeometricResonantLogTailMultiplier N a b 0 = 0 := by
  simp [d4HypergeometricResonantLogTailMultiplier]

theorem d4HypergeometricResonantLogTailMultiplier_succ (N : ℕ) (a b : ℂ) (k : ℕ) :
    d4HypergeometricResonantLogTailMultiplier N a b (k + 1) = d4HypergeometricResonantLogTailMultiplier N a b k +
      (a + (N : ℂ) + ((k + 1 : ℕ) : ℂ))⁻¹ +
      (b + (N : ℂ) + ((k + 1 : ℕ) : ℂ))⁻¹ -
      (((k + 1 : ℕ) : ℂ))⁻¹ -
      (((N + k + 2 : ℕ) : ℂ))⁻¹ := by
  rw [d4HypergeometricResonantLogTailMultiplier, d4HypergeometricResonantLogTailMultiplier, Finset.sum_range_succ]
  ring

theorem d4HypergeometricResonantRegularCoefficient_succ_recurrence (N : ℕ) (a b : ℂ) (k : ℕ) :
    ((k + 1 : ℕ) : ℂ) * (((N + 2 : ℕ) : ℂ) + (k : ℂ)) *
        d4HypergeometricResonantRegularCoefficient N a b (k + 1) =
      (a + ((N + 1 : ℕ) : ℂ) + (k : ℂ)) *
        (b + ((N + 1 : ℕ) : ℂ) + (k : ℂ)) * d4HypergeometricResonantRegularCoefficient N a b k := by
  unfold d4HypergeometricResonantRegularCoefficient
  apply ordinaryHypergeometricCoefficient_succ_recurrence
  · rw [ne_eq, ascPochhammer_eval_eq_zero_iff]
    push Not
    intro j hj h
    have hre := congrArg Complex.re h
    norm_num at hre
    have hj0 : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
    have hN0 : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith
  · intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    have hN0 : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
    have hk0 : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith

/-- Analytic tail coefficient, including the exact Frobenius logarithmic scale. -/
def d4HypergeometricResonantLogTailCoefficient (N : ℕ) (a b : ℂ) (k : ℕ) : ℂ :=
  d4HypergeometricResonantFrobeniusLogCoefficient N a b *
    d4HypergeometricResonantRegularCoefficient N a b k * d4HypergeometricResonantLogTailMultiplier N a b k

theorem d4HypergeometricResonantLogTailCoefficient_balance (N : ℕ) (a b : ℂ) (k : ℕ) (hk : 0 < k)
    (ha : a + (N : ℂ) + (k : ℂ) ≠ 0)
    (hb : b + (N : ℂ) + (k : ℂ) ≠ 0) :
    (((N + 1 : ℕ) : ℂ) + (k : ℂ)) * (k : ℂ) * d4HypergeometricResonantLogTailCoefficient N a b k -
        (a + (N : ℂ) + (k : ℂ)) * (b + (N : ℂ) + (k : ℂ)) *
          d4HypergeometricResonantLogTailCoefficient N a b (k - 1) +
        d4HypergeometricResonantFrobeniusLogCoefficient N a b *
          (((((N + 1 : ℕ) : ℂ) + 2 * (k : ℂ)) * d4HypergeometricResonantRegularCoefficient N a b k) -
            (a + b + 2 * (N : ℂ) + 2 * (k : ℂ)) * d4HypergeometricResonantRegularCoefficient N a b (k - 1)) = 0 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  have hrec := d4HypergeometricResonantRegularCoefficient_succ_recurrence N a b j
  have hja : a + (N : ℂ) + ((j : ℂ) + 1) ≠ 0 := by simpa [add_assoc] using ha
  have hjb : b + (N : ℂ) + ((j : ℂ) + 1) ≠ 0 := by simpa [add_assoc] using hb
  have hj1 : (j : ℂ) + 1 ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero j
  have hNj : (N : ℂ) + (j : ℂ) + 2 ≠ 0 := by
    exact_mod_cast (show N + j + 2 ≠ 0 by omega)
  let M : ℂ := (N : ℂ) + (j : ℂ) + 2
  let K : ℂ := (j : ℂ) + 1
  let A : ℂ := a + (N : ℂ) + (j : ℂ) + 1
  let B : ℂ := b + (N : ℂ) + (j : ℂ) + 1
  let F : ℂ := d4HypergeometricResonantRegularCoefficient N a b (j + 1)
  let G : ℂ := d4HypergeometricResonantRegularCoefficient N a b j
  have hrec' : M * K * F = A * B * G := by
    dsimp [M, K, A, B, F, G]
    push_cast at hrec
    convert hrec using 1 <;> ring
  have hA : A ≠ 0 := by simpa [A, add_assoc] using hja
  have hB : B ≠ 0 := by simpa [B, add_assoc] using hjb
  have hK : K ≠ 0 := by simpa [K] using hj1
  have hM : M ≠ 0 := by simpa [M, add_assoc] using hNj
  have hAterm : M * K * F * A⁻¹ = B * G := by
    rw [hrec']
    field_simp [hA]
  have hBterm : M * K * F * B⁻¹ = A * G := by
    rw [hrec']
    field_simp [hB]
  have hKterm : M * K * F * K⁻¹ = M * F := by
    field_simp [hK]
  have hMterm : M * K * F * M⁻¹ = K * F := by
    field_simp [hM]
  have hdelta :
      M * K * F * (A⁻¹ + B⁻¹ - K⁻¹ - M⁻¹) +
          (M + K) * F - (A + B) * G = 0 := by
    linear_combination hAterm + hBterm - hKterm - hMterm
  rw [Nat.succ_sub_one, d4HypergeometricResonantLogTailCoefficient, d4HypergeometricResonantLogTailCoefficient, d4HypergeometricResonantLogTailMultiplier_succ]
  push_cast
  dsimp [M, K, A, B, F, G] at hrec' hdelta
  linear_combination
    d4HypergeometricResonantFrobeniusLogCoefficient N a b *
      (d4HypergeometricResonantLogTailMultiplier N a b j * hrec' + hdelta)

open scoped PowerSeries

/-- Euler-form Gauss residual of an arbitrary complex formal power series. -/
def d4HypergeometricFormalEulerResidual (a b c : ℂ) (F : ℂ⟦X⟧) : ℂ⟦X⟧ :=
  hypergeometricEulerOperator (hypergeometricEulerOperator F) +
      PowerSeries.C (c - 1) * hypergeometricEulerOperator F -
    PowerSeries.X *
      (hypergeometricEulerOperator (hypergeometricEulerOperator F) +
        PowerSeries.C (a + b) * hypergeometricEulerOperator F +
        PowerSeries.C (a * b) * F)

@[simp] theorem d4HypergeometricFormalEulerResidual_coeff_zero (a b c : ℂ) (F : ℂ⟦X⟧) :
    PowerSeries.coeff 0 (d4HypergeometricFormalEulerResidual a b c F) = 0 := by
  rw [d4HypergeometricFormalEulerResidual, map_sub, map_add, map_add,
    coeff_hypergeometricEulerOperator, PowerSeries.coeff_C_mul,
    coeff_hypergeometricEulerOperator, PowerSeries.coeff_zero_X_mul]
  ring

theorem d4HypergeometricFormalEulerResidual_coeff_succ (a b c : ℂ) (F : ℂ⟦X⟧) (j : ℕ) :
    PowerSeries.coeff (j + 1) (d4HypergeometricFormalEulerResidual a b c F) =
      ((j + 1 : ℕ) : ℂ) * (c + (j : ℂ)) * PowerSeries.coeff (j + 1) F -
        (a + (j : ℂ)) * (b + (j : ℂ)) * PowerSeries.coeff j F := by
  rw [d4HypergeometricFormalEulerResidual, map_sub, map_add, map_add,
    coeff_hypergeometricEulerOperator, PowerSeries.coeff_C_mul,
    coeff_hypergeometricEulerOperator, coeff_X_mul_succ]
  simp only [map_add, add_mul, coeff_hypergeometricEulerOperator,
    PowerSeries.coeff_C_mul]
  push_cast
  ring

/-- Non-logarithmic forcing created when the Euler-form Gauss operator acts on `U log X`. -/
def d4HypergeometricFormalLogForcing (a b c : ℂ) (U : ℂ⟦X⟧) : ℂ⟦X⟧ :=
  PowerSeries.C 2 * hypergeometricEulerOperator U + PowerSeries.C (c - 1) * U -
    PowerSeries.X *
      (PowerSeries.C 2 * hypergeometricEulerOperator U + PowerSeries.C (a + b) * U)

theorem d4HypergeometricFormalLogForcing_coeff_zero (a b c : ℂ) (U : ℂ⟦X⟧) :
    PowerSeries.coeff 0 (d4HypergeometricFormalLogForcing a b c U) =
      (c - 1) * PowerSeries.coeff 0 U := by
  rw [d4HypergeometricFormalLogForcing, map_sub, map_add, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_zero_X_mul, PowerSeries.coeff_C_mul,
    coeff_hypergeometricEulerOperator]
  ring

theorem d4HypergeometricFormalLogForcing_coeff_succ (a b c : ℂ) (U : ℂ⟦X⟧) (j : ℕ) :
    PowerSeries.coeff (j + 1) (d4HypergeometricFormalLogForcing a b c U) =
      (2 * (((j + 1 : ℕ) : ℂ)) + c - 1) * PowerSeries.coeff (j + 1) U -
        (2 * (j : ℂ) + a + b) * PowerSeries.coeff j U := by
  rw [d4HypergeometricFormalLogForcing, map_sub, map_add, PowerSeries.coeff_C_mul,
    coeff_X_mul_succ, map_add, coeff_hypergeometricEulerOperator,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul,
    coeff_hypergeometricEulerOperator]
  push_cast
  ring

/-- Full coefficient sequence of `X^(N+1)` times the shifted regular Gauss series. -/
def d4HypergeometricResonantRegularBranchCoefficient (N : ℕ) (a b : ℂ) (j : ℕ) : ℂ :=
  if N < j then d4HypergeometricResonantRegularCoefficient N a b (j - (N + 1)) else 0

def d4HypergeometricResonantRegularBranchFormalPowerSeries (N : ℕ) (a b : ℂ) : ℂ⟦X⟧ :=
  PowerSeries.mk (d4HypergeometricResonantRegularBranchCoefficient N a b)

@[simp] theorem d4HypergeometricResonantRegularBranchFormalPowerSeries_coeff (N : ℕ) (a b : ℂ) (j : ℕ) :
    PowerSeries.coeff j (d4HypergeometricResonantRegularBranchFormalPowerSeries N a b) = d4HypergeometricResonantRegularBranchCoefficient N a b j := by
  simp [d4HypergeometricResonantRegularBranchFormalPowerSeries]

theorem d4HypergeometricResonantRegularBranchCoefficient_of_le (N : ℕ) (a b : ℂ) (j : ℕ) (hj : j ≤ N) :
    d4HypergeometricResonantRegularBranchCoefficient N a b j = 0 := by
  simp [d4HypergeometricResonantRegularBranchCoefficient, Nat.not_lt.mpr hj]

theorem d4HypergeometricResonantRegularBranchCoefficient_shift (N : ℕ) (a b : ℂ) (k : ℕ) :
    d4HypergeometricResonantRegularBranchCoefficient N a b (N + 1 + k) = d4HypergeometricResonantRegularCoefficient N a b k := by
  rw [d4HypergeometricResonantRegularBranchCoefficient, if_pos (by omega)]
  congr 1
  omega

/-- Analytic coefficient sequence of the normalized logarithmic companion. -/
def d4HypergeometricResonantCompanionAnalyticCoefficient (N : ℕ) (a b : ℂ) (j : ℕ) : ℂ :=
  if j ≤ N then d4HypergeometricResonantTruncationCoefficient N a b j
  else d4HypergeometricResonantLogTailCoefficient N a b (j - (N + 1))

def d4HypergeometricResonantCompanionAnalyticFormalPowerSeries (N : ℕ) (a b : ℂ) : ℂ⟦X⟧ :=
  PowerSeries.mk (d4HypergeometricResonantCompanionAnalyticCoefficient N a b)

@[simp] theorem d4HypergeometricResonantCompanionAnalyticFormalPowerSeries_coeff (N : ℕ) (a b : ℂ) (j : ℕ) :
    PowerSeries.coeff j (d4HypergeometricResonantCompanionAnalyticFormalPowerSeries N a b) = d4HypergeometricResonantCompanionAnalyticCoefficient N a b j := by
  simp [d4HypergeometricResonantCompanionAnalyticFormalPowerSeries]

theorem d4HypergeometricResonantCompanionAnalyticCoefficient_of_le (N : ℕ) (a b : ℂ) (j : ℕ) (hj : j ≤ N) :
    d4HypergeometricResonantCompanionAnalyticCoefficient N a b j =
      d4HypergeometricResonantTruncationCoefficient N a b j := by
  simp [d4HypergeometricResonantCompanionAnalyticCoefficient, hj]

theorem d4HypergeometricResonantCompanionAnalyticCoefficient_shift (N : ℕ) (a b : ℂ) (k : ℕ) :
    d4HypergeometricResonantCompanionAnalyticCoefficient N a b (N + 1 + k) = d4HypergeometricResonantLogTailCoefficient N a b k := by
  rw [d4HypergeometricResonantCompanionAnalyticCoefficient, if_neg (by omega)]
  congr 1
  omega

theorem d4HypergeometricResonantRegularBranchFormalPowerSeries_residual_eq_zero (N : ℕ) (a b : ℂ) :
    d4HypergeometricFormalEulerResidual a b (-(N : ℂ)) (d4HypergeometricResonantRegularBranchFormalPowerSeries N a b) = 0 := by
  apply PowerSeries.ext
  intro m
  cases m with
  | zero => simp
  | succ j =>
      rw [d4HypergeometricFormalEulerResidual_coeff_succ, map_zero]
      by_cases hjN : j < N
      · rw [d4HypergeometricResonantRegularBranchFormalPowerSeries_coeff, d4HypergeometricResonantRegularBranchFormalPowerSeries_coeff,
          d4HypergeometricResonantRegularBranchCoefficient_of_le N a b j (by omega),
          d4HypergeometricResonantRegularBranchCoefficient_of_le N a b (j + 1) (by omega)]
        ring
      · by_cases hjeq : j = N
        · subst j
          rw [d4HypergeometricResonantRegularBranchFormalPowerSeries_coeff, d4HypergeometricResonantRegularBranchFormalPowerSeries_coeff,
            d4HypergeometricResonantRegularBranchCoefficient_of_le N a b N (by omega)]
          have hshift := d4HypergeometricResonantRegularBranchCoefficient_shift N a b 0
          rw [show N + 1 = N + 1 + 0 by omega, hshift]
          push_cast
          ring
        · have hNj : N < j := by omega
          obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hNj
          subst j
          rw [d4HypergeometricResonantRegularBranchFormalPowerSeries_coeff, d4HypergeometricResonantRegularBranchFormalPowerSeries_coeff,
            show N.succ + k = N + 1 + k by omega,
            d4HypergeometricResonantRegularBranchCoefficient_shift,
            show N.succ + k + 1 = N + 1 + (k + 1) by omega,
            d4HypergeometricResonantRegularBranchCoefficient_shift]
          have hrec := d4HypergeometricResonantRegularCoefficient_succ_recurrence N a b k
          push_cast at hrec ⊢
          linear_combination hrec

/-- Exact formal logarithmic-companion equation. The first summand is the analytic-part residual;
the second is the non-logarithmic forcing of the regular branch times the unique Frobenius scale. -/
theorem d4HypergeometricResonantLogarithmicCompanion_formalEquation (N : ℕ) (a b : ℂ)
    (ha : ∀ k : ℕ, 0 < k → a + (N : ℂ) + (k : ℂ) ≠ 0)
    (hb : ∀ k : ℕ, 0 < k → b + (N : ℂ) + (k : ℂ) ≠ 0) :
    d4HypergeometricFormalEulerResidual a b (-(N : ℂ)) (d4HypergeometricResonantCompanionAnalyticFormalPowerSeries N a b) +
        PowerSeries.C (d4HypergeometricResonantFrobeniusLogCoefficient N a b) *
          d4HypergeometricFormalLogForcing a b (-(N : ℂ)) (d4HypergeometricResonantRegularBranchFormalPowerSeries N a b) = 0 := by
  apply PowerSeries.ext
  intro m
  cases m with
  | zero =>
      rw [map_add, d4HypergeometricFormalEulerResidual_coeff_zero, PowerSeries.coeff_C_mul,
        d4HypergeometricFormalLogForcing_coeff_zero, d4HypergeometricResonantRegularBranchFormalPowerSeries_coeff,
        d4HypergeometricResonantRegularBranchCoefficient_of_le N a b 0 (by omega), map_zero]
      ring
  | succ j =>
      rw [map_add, d4HypergeometricFormalEulerResidual_coeff_succ, PowerSeries.coeff_C_mul,
        d4HypergeometricFormalLogForcing_coeff_succ, map_zero]
      by_cases hjN : j < N
      · rw [d4HypergeometricResonantCompanionAnalyticFormalPowerSeries_coeff, d4HypergeometricResonantCompanionAnalyticFormalPowerSeries_coeff,
          d4HypergeometricResonantCompanionAnalyticCoefficient_of_le N a b j (by omega),
          d4HypergeometricResonantCompanionAnalyticCoefficient_of_le N a b (j + 1) (by omega),
          d4HypergeometricResonantRegularBranchFormalPowerSeries_coeff, d4HypergeometricResonantRegularBranchFormalPowerSeries_coeff,
          d4HypergeometricResonantRegularBranchCoefficient_of_le N a b j (by omega),
          d4HypergeometricResonantRegularBranchCoefficient_of_le N a b (j + 1) (by omega)]
        have hrec :=
          d4HypergeometricResonantTruncationCoefficient_succ_recurrence
            N a b j hjN
        push_cast at hrec ⊢
        linear_combination hrec
      · by_cases hjeq : j = N
        · subst j
          rw [d4HypergeometricResonantCompanionAnalyticFormalPowerSeries_coeff, d4HypergeometricResonantCompanionAnalyticFormalPowerSeries_coeff,
            d4HypergeometricResonantCompanionAnalyticCoefficient_of_le N a b N (by omega),
            show N + 1 = N + 1 + 0 by omega, d4HypergeometricResonantCompanionAnalyticCoefficient_shift,
            d4HypergeometricResonantRegularBranchFormalPowerSeries_coeff, d4HypergeometricResonantRegularBranchFormalPowerSeries_coeff,
            d4HypergeometricResonantRegularBranchCoefficient_of_le N a b N (by omega),
            show N + 1 = N + 1 + 0 by omega, d4HypergeometricResonantRegularBranchCoefficient_shift,
            d4HypergeometricResonantLogTailCoefficient, d4HypergeometricResonantLogTailMultiplier_zero, mul_zero,
            d4HypergeometricResonantTruncationCoefficient_top]
          have hbal :=
            d4HypergeometricResonantFrobeniusLogCoefficient_terminalBalance N a b
          simp [d4HypergeometricResonantRegularCoefficient, ordinaryHypergeometricCoefficient] at hbal ⊢
          linear_combination hbal
        · have hNj : N < j := by omega
          obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hNj
          rw [d4HypergeometricResonantCompanionAnalyticFormalPowerSeries_coeff, d4HypergeometricResonantCompanionAnalyticFormalPowerSeries_coeff,
            show N.succ + k = N + 1 + k by omega, d4HypergeometricResonantCompanionAnalyticCoefficient_shift,
            show N.succ + k + 1 = N + 1 + (k + 1) by omega,
            d4HypergeometricResonantCompanionAnalyticCoefficient_shift,
            d4HypergeometricResonantRegularBranchFormalPowerSeries_coeff, d4HypergeometricResonantRegularBranchFormalPowerSeries_coeff,
            d4HypergeometricResonantRegularBranchCoefficient_shift, d4HypergeometricResonantRegularBranchCoefficient_shift]
          have htail := d4HypergeometricResonantLogTailCoefficient_balance N a b (k + 1) (by omega)
            (ha (k + 1) (by omega)) (hb (k + 1) (by omega))
          push_cast at htail ⊢
          linear_combination htail

/-- Physical mixed BM first parameter avoids every post-collision tail denominator. -/
theorem d4BMMixedHorizonComplexA_add_order_add_ne_zero
    (n k : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) (r : ℕ) (hr : 0 < r) :
    d4BMMixedHorizonComplexA n k chi +
        (d4BMMixedHorizonFrobeniusOrder n k : ℂ) + (r : ℂ) ≠ 0 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  have h := (d4BMMixedHorizonShiftedRegularParameters_ne_negNat
    n k chi hchi j).1
  rw [d4BMMixedHorizonShiftedRegularA] at h
  intro hzero
  apply h
  push_cast at hzero
  push_cast
  linear_combination hzero

/-- Physical mixed BM second parameter avoids every post-collision tail denominator. -/
theorem d4BMMixedHorizonComplexB_add_order_add_ne_zero
    (n k : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) (r : ℕ) (hr : 0 < r) :
    d4BMMixedHorizonComplexB n k chi +
        (d4BMMixedHorizonFrobeniusOrder n k : ℂ) + (r : ℂ) ≠ 0 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  have h := (d4BMMixedHorizonShiftedRegularParameters_ne_negNat
    n k chi hchi j).2.1
  rw [d4BMMixedHorizonShiftedRegularB] at h
  intro hzero
  apply h
  push_cast at hzero
  push_cast
  linear_combination hzero

/-- Literal physical mixed BM parameters carry the exact formal logarithmic companion equation. -/
theorem d4BMMixedHorizonLogarithmicCompanion_formalEquation
    (n k : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) :
    d4HypergeometricFormalEulerResidual
          (d4BMMixedHorizonComplexA n k chi)
          (d4BMMixedHorizonComplexB n k chi)
          (d4BMCausalRadialC (d4BMCausalPlusMinusFrequency n k chi))
          (d4HypergeometricResonantCompanionAnalyticFormalPowerSeries
            (d4BMMixedHorizonFrobeniusOrder n k)
            (d4BMMixedHorizonComplexA n k chi)
            (d4BMMixedHorizonComplexB n k chi)) +
        PowerSeries.C
            (d4HypergeometricResonantFrobeniusLogCoefficient
              (d4BMMixedHorizonFrobeniusOrder n k)
              (d4BMMixedHorizonComplexA n k chi)
              (d4BMMixedHorizonComplexB n k chi)) *
          d4HypergeometricFormalLogForcing
            (d4BMMixedHorizonComplexA n k chi)
            (d4BMMixedHorizonComplexB n k chi)
            (d4BMCausalRadialC (d4BMCausalPlusMinusFrequency n k chi))
            (d4HypergeometricResonantRegularBranchFormalPowerSeries
              (d4BMMixedHorizonFrobeniusOrder n k)
              (d4BMMixedHorizonComplexA n k chi)
              (d4BMMixedHorizonComplexB n k chi)) = 0 := by
  rw [d4BMCausalRadialC_plusMinus_eq_negNat]
  simpa [d4BMMixedHorizonFrobeniusOrder] using
    d4HypergeometricResonantLogarithmicCompanion_formalEquation
      (d4BMMixedHorizonFrobeniusOrder n k)
      (d4BMMixedHorizonComplexA n k chi)
      (d4BMMixedHorizonComplexB n k chi)
      (d4BMMixedHorizonComplexA_add_order_add_ne_zero n k chi hchi)
      (d4BMMixedHorizonComplexB_add_order_add_ne_zero n k chi hchi)

end
end RHTower
