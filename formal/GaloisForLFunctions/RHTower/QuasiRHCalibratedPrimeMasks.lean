import GaloisForLFunctions.RHTower.WeilWorkSettledPhasePrimeDeletionVariance

/-!
# Optimal prime coprimality masks with prescribed mean

The exact prime covariance gives a completed-square identity. At mean one,
coefficients `p / ∑ (p - 1)` uniquely minimize the variance, which equals
`1 / ∑ (p - 1)`. The last theorem transfers this value to the literal
right-radial square mean. No finite-window or detector-transfer estimate is assumed.
-/

open Finset Filter
open scoped Topology
noncomputable section
namespace RHTower.WeilSingularArithmetic

/-- Total reciprocal-variance capacity of the normalized prime masks. -/
def primeMaskCapacity (S : Finset ℕ) : ℝ := ∑ p ∈ S, ((p : ℝ) - 1)

def primeMaskMean (S : Finset ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ p ∈ S, c p * coprimeDensity p

def primeMaskVariance (S : Finset ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ p ∈ S, ∑ q ∈ S, c p * c q *
    (coprimeDensity (p * q) - coprimeDensity p * coprimeDensity q)

def calibratedPrimeMaskCoefficient (S : Finset ℕ) (p : ℕ) : ℝ :=
  (p : ℝ) / primeMaskCapacity S

/-- Literal arithmetic mask; its coefficients are nonnegative. -/
def calibratedPrimeMask (S : Finset ℕ) (n : ℕ) : ℝ :=
  ∑ p ∈ S, calibratedPrimeMaskCoefficient S p * coprimeMask p n

theorem primeMaskCapacity_pos (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (hne : S.Nonempty) : 0 < primeMaskCapacity S := by
  apply Finset.sum_pos _ hne
  intro p hp
  have : (1 : ℝ) < p := by exact_mod_cast (hS p hp).one_lt
  linarith

theorem primeMaskMean_eq (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (c : ℕ → ℝ) :
    primeMaskMean S c = ∑ p ∈ S, ((p : ℝ) - 1) * (c p / p) := by
  apply Finset.sum_congr rfl
  intro p hp
  rw [coprimeDensity_prime (hS p hp)]
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (hS p hp).ne_zero
  field_simp

theorem primeMaskVariance_eq (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (c : ℕ → ℝ) :
    primeMaskVariance S c = ∑ p ∈ S, ((p : ℝ) - 1) * (c p / p) ^ 2 := by
  rw [primeMaskVariance, coprimeCovariance_primes_diagonal S hS]
  apply Finset.sum_congr rfl
  intro p _
  ring

/-- Exact variance excess above the best value at the same mean. -/
theorem primeMaskVariance_decomposition (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (hne : S.Nonempty) (c : ℕ → ℝ) :
    primeMaskVariance S c = primeMaskMean S c ^ 2 / primeMaskCapacity S +
      ∑ p ∈ S, ((p : ℝ) - 1) *
        (c p / p - primeMaskMean S c / primeMaskCapacity S) ^ 2 := by
  have hA := (primeMaskCapacity_pos S hS hne).ne'
  have hterm (p : ℕ) : ((p : ℝ) - 1) *
      (c p / p - primeMaskMean S c / primeMaskCapacity S) ^ 2 =
      ((p : ℝ) - 1) * (c p / p) ^ 2 -
        (2 * primeMaskMean S c / primeMaskCapacity S) * (((p : ℝ) - 1) * (c p / p)) +
        (primeMaskMean S c / primeMaskCapacity S) ^ 2 * ((p : ℝ) - 1) := by ring
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← primeMaskVariance_eq S hS c,
    ← primeMaskMean_eq S hS c]
  change primeMaskVariance S c = _ +
    (primeMaskVariance S c - (2 * primeMaskMean S c / primeMaskCapacity S) *
      primeMaskMean S c + (primeMaskMean S c / primeMaskCapacity S) ^ 2 * primeMaskCapacity S)
  field_simp
  ring

/-- The covariance lower bound is attained only by the calibrated coefficients. -/
theorem primeMaskVariance_sharp (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (hne : S.Nonempty) (c : ℕ → ℝ) :
    primeMaskMean S c ^ 2 / primeMaskCapacity S ≤ primeMaskVariance S c ∧
      (primeMaskVariance S c = primeMaskMean S c ^ 2 / primeMaskCapacity S ↔
        ∀ p ∈ S, c p = primeMaskMean S c * calibratedPrimeMaskCoefficient S p) := by
  have hn (p : ℕ) (hp : p ∈ S) : 0 ≤ ((p : ℝ) - 1) *
      (c p / p - primeMaskMean S c / primeMaskCapacity S) ^ 2 := by
    have : (1 : ℝ) < p := by exact_mod_cast (hS p hp).one_lt
    exact mul_nonneg (by linarith) (sq_nonneg _)
  have hsum := Finset.sum_nonneg hn
  have hdec := primeMaskVariance_decomposition S hS hne c
  refine ⟨by linarith, ?_⟩
  constructor
  · intro h
    have hz : (∑ p ∈ S, ((p : ℝ) - 1) *
        (c p / p - primeMaskMean S c / primeMaskCapacity S) ^ 2) = 0 := by linarith
    intro p hp
    have he := (Finset.sum_eq_zero_iff_of_nonneg hn).mp hz p hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (hS p hp).one_lt
    have hw : (p : ℝ) - 1 ≠ 0 := by linarith
    have hs := (mul_eq_zero.mp he).resolve_left hw
    rw [pow_two] at hs
    have hd := sub_eq_zero.mp (mul_self_eq_zero.mp hs)
    have hp0 : (p : ℝ) ≠ 0 := by linarith
    have hh := (div_eq_iff hp0).mp hd
    rw [hh, calibratedPrimeMaskCoefficient]
    ring
  · intro h
    have hz : (∑ p ∈ S, ((p : ℝ) - 1) *
        (c p / p - primeMaskMean S c / primeMaskCapacity S) ^ 2) = 0 := by
      apply Finset.sum_eq_zero
      intro p hp
      rw [h p hp, calibratedPrimeMaskCoefficient]
      have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (hS p hp).ne_zero
      have he : primeMaskMean S c * ((p : ℝ) / primeMaskCapacity S) / p =
          primeMaskMean S c / primeMaskCapacity S := by field_simp
      rw [he, sub_self, zero_pow (by decide : 2 ≠ 0), mul_zero]
    linarith

theorem calibratedPrimeMask_mean (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (hne : S.Nonempty) : primeMaskMean S (calibratedPrimeMaskCoefficient S) = 1 := by
  have hA := (primeMaskCapacity_pos S hS hne).ne'
  rw [primeMaskMean_eq S hS]
  calc
    _ = ∑ p ∈ S, ((p : ℝ) - 1) / primeMaskCapacity S := by
      apply Finset.sum_congr rfl
      intro p hp
      have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (hS p hp).ne_zero
      unfold calibratedPrimeMaskCoefficient
      field_simp
    _ = primeMaskCapacity S / primeMaskCapacity S := by rw [← Finset.sum_div]; rfl
    _ = 1 := div_self hA

theorem calibratedPrimeMask_variance (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (hne : S.Nonempty) :
    primeMaskVariance S (calibratedPrimeMaskCoefficient S) = 1 / primeMaskCapacity S := by
  have h := (primeMaskVariance_sharp S hS hne (calibratedPrimeMaskCoefficient S)).2
  rw [calibratedPrimeMask_mean S hS hne, one_pow] at h
  exact h.mpr (by intro p _; simp)

/-- The optimizer has bounded coefficient mass without a prime-counting estimate. -/
theorem calibratedPrimeMask_coefficient_mass (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (hne : S.Nonempty) :
    (∑ p ∈ S, calibratedPrimeMaskCoefficient S p) =
      1 + (S.card : ℝ) / primeMaskCapacity S := by
  have hA := (primeMaskCapacity_pos S hS hne).ne'
  have he : (∑ p ∈ S, (p : ℝ)) = primeMaskCapacity S + S.card := by
    unfold primeMaskCapacity
    rw [Finset.sum_sub_distrib]
    simp
  simp only [calibratedPrimeMaskCoefficient, ← Finset.sum_div]
  rw [he, add_div, div_self hA]

theorem primeMaskCapacity_ge_card_mul (S : Finset ℕ) (R : ℝ)
    (hR : ∀ p ∈ S, R ≤ (p : ℝ)) :
    (S.card : ℝ) * (R - 1) ≤ primeMaskCapacity S := by
  have h := Finset.sum_le_sum (fun p hp => sub_le_sub_right (hR p hp) 1)
  simpa only [Finset.sum_const, nsmul_eq_mul, primeMaskCapacity] using h

/-- Exact right-radial square mean of the literal normalized mask minus one. -/
theorem calibratedPrimeMask_centered_square_residue (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (hne : S.Nonempty) :
    Tendsto (fun s : ℝ => (s - 1) * ∑' n : ℕ,
      ‖((calibratedPrimeMask S n - 1 : ℝ) : ℂ)‖ ^ 2 / (n : ℝ) ^ s)
      (𝓝[>] 1) (𝓝 (1 / primeMaskCapacity S)) := by
  have hd := coprimeAffineSquareDensity_centered S id (calibratedPrimeMaskCoefficient S)
  change coprimeAffineSquareDensity S id (calibratedPrimeMaskCoefficient S)
    (-primeMaskMean S (calibratedPrimeMaskCoefficient S)) =
      primeMaskVariance S (calibratedPrimeMaskCoefficient S) at hd
  rw [calibratedPrimeMask_mean S hS hne, calibratedPrimeMask_variance S hS hne] at hd
  have h := coprimeAffineMask_square_residue S id (fun p hp => (hS p hp).ne_zero)
    (calibratedPrimeMaskCoefficient S) (-1)
  rw [hd] at h
  have he : coprimeAffineMask S id (calibratedPrimeMaskCoefficient S) (-1) =
      fun n => calibratedPrimeMask S n - 1 := by
    funext n
    simp only [coprimeAffineMask, calibratedPrimeMask, id_eq]
    ring
  rwa [he] at h

end RHTower.WeilSingularArithmetic
