import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaAnomalyBurnolSingularQuotient
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmTwoPrimeBezoutGrowthNoGo

/-!
# The Burnol anomaly frame is algebraically unimodular but analytically singular

The completed Gamma/co-Poisson cells of the theta anomaly are exactly the existing entire
prime-window multipliers, including at the removable origin.  Consequently the prime-two and
prime-three Burnol cells generate the unit ideal in the ring of entire functions.

This algebraic corona has unavoidable analytic cost.  On the positive real spectral boundary,
every synthesis of one from the two Burnol cells has coefficient norm at least linear in the
frequency: `max ‖b₂(t)‖ ‖b₃(t)‖ ≥ t/4`.  Thus P-G111's singular reporter cannot extend through a
bounded finite-prime Hilbert multiplier.  The positive survivor is an exact algebraic synthesis
with a forced order-one graph-topology loss.
-/

open Complex Real Filter Topology

namespace RHTower.HedenmalmThetaSource

noncomputable section

/-- The Gamma/co-Poisson completion is the entire centered multiplier at every spectral point,
including the removable origin. -/
theorem burnolCompletedCenteredMultiplier_eq_centeredMultiplierE
    (n : ℕ) (z : ℂ) :
    burnolCompletedCenteredMultiplier n z = centeredMultiplierE n z := by
  rcases eq_or_ne z 0 with rfl | hz
  · rw [burnolCompletedCenteredMultiplier_zero, centeredMultiplierE_at_zero,
      thetaIntegerShiftScale]
    push_cast
    ring
  · rw [burnolCompletedCenteredMultiplier_eq_centeredMultiplier n hz,
      centeredMultiplierE_eq n hz]

/-- **Burnol algebraic corona.**  The completed prime-two and prime-three Gamma/co-Poisson anomaly
cells generate the unit ideal in the ring of entire functions. -/
theorem exists_burnol_completed_two_prime_bezout :
    ∃ b₂ b₃ : ℂ → ℂ, Differentiable ℂ b₂ ∧ Differentiable ℂ b₃ ∧
      ∀ z : ℂ,
        b₂ z * burnolCompletedCenteredMultiplier 2 z +
          b₃ z * burnolCompletedCenteredMultiplier 3 z = 1 := by
  obtain ⟨b₂, b₃, hb₂, hb₃, hbez⟩ := exists_two_prime_bezout
  refine ⟨b₂, b₃, hb₂, hb₃, fun z => ?_⟩
  rw [burnolCompletedCenteredMultiplier_eq_centeredMultiplierE,
    burnolCompletedCenteredMultiplier_eq_centeredMultiplierE]
  exact hbez z

/-- Each completed Burnol cell has order-one real-axis decay. -/
theorem norm_burnolCompletedCenteredMultiplier_real_le
    (n : ℕ) {t : ℝ} (ht : t ≠ 0) :
    ‖burnolCompletedCenteredMultiplier n (t : ℂ)‖ ≤
      2 * ((n : ℝ) ^ (-(1 / 2 : ℝ))) / |t| := by
  rw [burnolCompletedCenteredMultiplier_eq_centeredMultiplierE,
    centeredMultiplierE_eq n (by exact_mod_cast ht)]
  exact norm_centeredMultiplier_le n ht

/-- **Quantitative corona escape.**  Every pointwise synthesis of one by the completed prime-two
and prime-three Burnol cells pays at least linear coefficient growth on the positive real axis.
No regularity assumption on the coefficients is used. -/
theorem burnol_two_prime_bezout_linear_escape
    (b₂ b₃ : ℝ → ℂ) {t : ℝ} (ht : 0 < t)
    (hbez :
      b₂ t * burnolCompletedCenteredMultiplier 2 (t : ℂ) +
        b₃ t * burnolCompletedCenteredMultiplier 3 (t : ℂ) = 1) :
    t / 4 ≤ max ‖b₂ t‖ ‖b₃ t‖ := by
  let M : ℝ := max ‖b₂ t‖ ‖b₃ t‖
  have hM2 : ‖b₂ t‖ ≤ M := le_max_left _ _
  have hM3 : ‖b₃ t‖ ≤ M := le_max_right _ _
  have hM : 0 ≤ M := (norm_nonneg _).trans hM2
  have ht0 : t ≠ 0 := ne_of_gt ht
  have h2raw := norm_burnolCompletedCenteredMultiplier_real_le 2 ht0
  have h3raw := norm_burnolCompletedCenteredMultiplier_real_le 3 ht0
  have hpow2 : ((2 : ℝ) ^ (-(1 / 2 : ℝ))) ≤ 1 := by
    exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hpow3 : ((3 : ℝ) ^ (-(1 / 2 : ℝ))) ≤ 1 := by
    exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have habs : |t| = t := abs_of_pos ht
  have h2 : ‖burnolCompletedCenteredMultiplier 2 (t : ℂ)‖ ≤ 2 / t := by
    rw [habs] at h2raw
    exact h2raw.trans (div_le_div_of_nonneg_right (by nlinarith) ht.le)
  have h3 : ‖burnolCompletedCenteredMultiplier 3 (t : ℂ)‖ ≤ 2 / t := by
    rw [habs] at h3raw
    exact h3raw.trans (div_le_div_of_nonneg_right (by nlinarith) ht.le)
  have htri := norm_add_le
    (b₂ t * burnolCompletedCenteredMultiplier 2 (t : ℂ))
    (b₃ t * burnolCompletedCenteredMultiplier 3 (t : ℂ))
  rw [hbez, norm_one, norm_mul, norm_mul] at htri
  have hp2 : ‖b₂ t‖ * ‖burnolCompletedCenteredMultiplier 2 (t : ℂ)‖ ≤ M * (2 / t) :=
    mul_le_mul hM2 h2 (norm_nonneg _) hM
  have hp3 : ‖b₃ t‖ * ‖burnolCompletedCenteredMultiplier 3 (t : ℂ)‖ ≤ M * (2 / t) :=
    mul_le_mul hM3 h3 (norm_nonneg _) hM
  have hfour : 1 ≤ M * (4 / t) := by
    calc
      1 ≤ ‖b₂ t‖ * ‖burnolCompletedCenteredMultiplier 2 (t : ℂ)‖ +
          ‖b₃ t‖ * ‖burnolCompletedCenteredMultiplier 3 (t : ℂ)‖ := htri
      _ ≤ M * (2 / t) + M * (2 / t) := add_le_add hp2 hp3
      _ = M * (4 / t) := by ring
  have ht4 : t ≤ M * 4 := by
    rw [show M * (4 / t) = (M * 4) / t by ring] at hfour
    have hh : 1 * t ≤ M * 4 := (le_div_iff₀ ht).mp (by simpa using hfour)
    nlinarith
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 4)]
  simpa only [M, mul_comm] using ht4

/-- Global version of quantitative escape: a synthesis pair cannot be bounded, and exceeds every
prescribed coefficient ceiling at an explicit positive frequency. -/
theorem burnol_two_prime_bezout_coefficients_unbounded
    (b₂ b₃ : ℝ → ℂ)
    (hbez : ∀ t : ℝ,
      b₂ t * burnolCompletedCenteredMultiplier 2 (t : ℂ) +
        b₃ t * burnolCompletedCenteredMultiplier 3 (t : ℂ) = 1)
    (C : ℝ) :
    ∃ t : ℝ, 0 < t ∧ C < max ‖b₂ t‖ ‖b₃ t‖ := by
  let t : ℝ := 4 * (max C 0 + 1)
  have ht : 0 < t := by
    dsimp only [t]
    positivity
  have hlin := burnol_two_prime_bezout_linear_escape b₂ b₃ ht (hbez t)
  refine ⟨t, ht, ?_⟩
  have hCt : C < t / 4 := by
    dsimp only [t]
    rw [mul_div_cancel_left₀ _ (by norm_num : (4 : ℝ) ≠ 0)]
    linarith [le_max_left C 0]
  exact hCt.trans_le hlin

/-- Algebraic synthesis exists, but every entire synthesis has forced linear real-axis escape. -/
theorem exists_burnol_completed_entire_bezout_with_linear_escape :
    ∃ b₂ b₃ : ℂ → ℂ, Differentiable ℂ b₂ ∧ Differentiable ℂ b₃ ∧
      (∀ z : ℂ,
        b₂ z * burnolCompletedCenteredMultiplier 2 z +
          b₃ z * burnolCompletedCenteredMultiplier 3 z = 1) ∧
      (∀ t : ℝ, 0 < t → t / 4 ≤ max ‖b₂ (t : ℂ)‖ ‖b₃ (t : ℂ)‖) := by
  obtain ⟨b₂, b₃, hb₂, hb₃, hbez⟩ := exists_burnol_completed_two_prime_bezout
  refine ⟨b₂, b₃, hb₂, hb₃, hbez, ?_⟩
  intro t ht
  exact burnol_two_prime_bezout_linear_escape
    (fun s : ℝ => b₂ (s : ℂ)) (fun s : ℝ => b₃ (s : ℂ)) ht (hbez (t : ℂ))

end


end RHTower.HedenmalmThetaSource
