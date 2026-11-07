import GaloisForLFunctions.SumProductArithmeticOfTheLogarithm.PositiveNearCountEffectiveAverage

/-!
# Explicit rates for the profile average and the integral count

Choosing the resolution as `floor(log Y / log 16)` balances the profile
modulus against its finite return cost. The uniform profile error is at most
`profileRateConstant * log(log n) / log n` beyond `profileRateThreshold`.

For the actual generalized-integer count, the same choice at `Y = log x`
gives an explicit `log(log(log x)) / log(log x)` error in the leading
integrated-deficit coefficient. Constants and cutoffs are defined below.
-/

noncomputable section
open scoped BigOperators Classical
namespace GaloisForLFunctions.SumProductArithmeticOfTheLogarithm.PositiveNearCount

/-- A constant for the optimized uniform profile estimate. -/
def profileRateConstant : ℝ := 2 * Real.log 16 * (8 + 33 * Real.log 4 + 2 / 3)

/-- A fixed threshold at which the logarithmic resolution choice has at least two cells. -/
def profileRateThreshold : ℝ := max 256 (Real.exp (Real.exp 1))

theorem profileRateConstant_pos : 0 < profileRateConstant := by
  have h4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have h16 : 0 < Real.log 16 := Real.log_pos (by norm_num)
  dsimp only [profileRateConstant]
  positivity

private theorem log_sixteen_ge_one : 1 ≤ Real.log 16 := by
  have h := _root_.HTGeometry.one_sub_inv_le_log (by norm_num : (0 : ℝ) < 4)
  norm_num at h
  have he : Real.log 16 = 2 * Real.log 4 := by
    rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [he]
  linarith only [h]

private theorem rate_scale_bounds {Y : ℝ} (hY : profileRateThreshold ≤ Y) :
    1 < Y ∧ 2 * Real.log 16 ≤ Real.log Y ∧ 1 ≤ Real.log (Real.log Y) := by
  have h256 : (256 : ℝ) ≤ Y := (le_max_left _ _).trans hY
  have hExp : Real.exp (Real.exp 1) ≤ Y := (le_max_right _ _).trans hY
  refine ⟨by linarith only [h256], ?_, ?_⟩
  · have h := Real.log_le_log (by norm_num : (0 : ℝ) < 256) h256
    have he : Real.log 256 = 2 * Real.log 16 := by
      rw [show (256 : ℝ) = 16 ^ 2 by norm_num, Real.log_pow]
      norm_num
    rwa [he] at h
  · have h := Real.log_le_log (Real.exp_pos _) hExp
    rw [Real.log_exp] at h
    have hh := Real.log_le_log (Real.exp_pos 1) h
    rwa [Real.log_exp] at hh

private theorem nat_le_two_pow (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have h1 : 1 ≤ (2 : ℕ) ^ n := pow_pos (by norm_num : (0 : ℕ) < 2) n
    rw [pow_succ]
    omega

private theorem sq_le_four_pow (n : ℕ) : (n : ℝ) ^ 2 ≤ (4 : ℝ) ^ n := by
  have h : (n : ℕ) ^ 2 ≤ 4 ^ n := by
    calc
      _ = n * n := by rw [pow_two]
      _ ≤ (2 : ℕ) ^ n * 2 ^ n := Nat.mul_le_mul (nat_le_two_pow n) (nat_le_two_pow n)
      _ = _ := by rw [← mul_pow]; norm_num
  exact_mod_cast h

/-- Optimizing the explicit resolution and return costs gives a logarithmic convergence rate. -/
theorem exists_resolution_for_log_rate {Y : ℝ} (hY : profileRateThreshold ≤ Y) :
    ∃ Q : ℕ, 2 ≤ Q ∧ resolutionError Q + returnCost Q / Y ≤
      profileRateConstant * Real.log (Real.log Y) / Real.log Y := by
  obtain ⟨hy1, hlow, hloglog⟩ := rate_scale_bounds hY
  have hy0 : 0 < Y := zero_lt_one.trans hy1
  have hL : 0 < Real.log Y := Real.log_pos hy1
  have hp : 0 < Real.log 16 := Real.log_pos (by norm_num)
  have h4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  let Q := ⌊Real.log Y / Real.log 16⌋₊
  have hhi : Real.log Y / Real.log 16 < (Q : ℝ) + 1 := Nat.lt_floor_add_one _
  have hfloor : (Q : ℝ) ≤ Real.log Y / Real.log 16 := Nat.floor_le (div_pos hL hp).le
  have hQ : 2 ≤ Q := by
    by_contra hQ
    have hqr : (Q : ℝ) ≤ 1 := by exact_mod_cast (show Q ≤ 1 by omega)
    have hratio : (2 : ℝ) ≤ Real.log Y / Real.log 16 := (le_div_iff₀ hp).mpr hlow
    linarith only [hhi, hqr, hratio]
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast (show 1 ≤ Q by omega)
  have hQ0 : (0 : ℝ) < Q := zero_lt_one.trans_le hQ1
  have hQL : (Q : ℝ) ≤ Real.log Y := by
    apply hfloor.trans
    apply (div_le_iff₀ hp).mpr
    have h := mul_nonneg hL.le (sub_nonneg.mpr log_sixteen_ge_one)
    nlinarith only [h]
  have hrec : 1 / (Q : ℝ) ≤ 2 * Real.log 16 / Real.log Y := by
    apply (div_le_div_iff₀ hQ0 hL).mpr
    have h := (div_lt_iff₀ hp).mp hhi
    have hh := mul_nonneg hp.le (sub_nonneg.mpr hQ1)
    nlinarith only [h, hh]
  -- The fourth-power scale dominates the square of the resolution index.
  have hcut : (16 : ℝ) ^ Q ≤ Y :=
    (pow_log_floor_bracket (b := (16 : ℝ)) (by norm_num) hy1.le).1
  have hsq := sq_le_four_pow Q
  have hB : returnCost Q / Y ≤ Real.log 4 / (Q : ℝ) := by
    calc
      _ ≤ returnCost Q / (16 : ℝ) ^ Q :=
        div_le_div_of_nonneg_left (returnCost_nonneg Q) (by positivity) hcut
      _ = (Q : ℝ) * Real.log 4 / (4 * (4 : ℝ) ^ Q) := by
        dsimp only [returnCost]
        rw [show (16 : ℝ) ^ Q = (4 : ℝ) ^ Q * 4 ^ Q by rw [← mul_pow]; norm_num]
        field_simp
      _ ≤ Real.log 4 / (4 * (Q : ℝ)) := by
        apply (div_le_div_iff₀ (by positivity : 0 < 4 * (4 : ℝ) ^ Q)
          (by positivity : 0 < 4 * (Q : ℝ))).mpr
        have h := mul_le_mul_of_nonneg_right hsq h4.le
        nlinarith only [h]
      _ ≤ Real.log 4 / (Q : ℝ) :=
        div_le_div_of_nonneg_left h4.le hQ0 (by linarith only [hQ0])
  have hlogQ : Real.log (Q : ℝ) ≤ Real.log (Real.log Y) := Real.log_le_log hQ0 hQL
  have hloglog0 : 0 ≤ Real.log (Real.log Y) := zero_le_one.trans hloglog
  have hnum : 8 * Real.log (Q : ℝ) + 33 * Real.log 4 + 2 / 3 ≤
      (8 + 33 * Real.log 4 + 2 / 3) * Real.log (Real.log Y) := by
    have h := mul_le_mul_of_nonneg_left hloglog
      (by positivity : 0 ≤ 33 * Real.log 4 + 2 / 3)
    nlinarith only [hlogQ, h]
  refine ⟨Q, hQ, ?_⟩
  calc
    _ ≤ resolutionError Q + Real.log 4 / (Q : ℝ) := add_le_add le_rfl hB
    _ = (8 * Real.log (Q : ℝ) + 33 * Real.log 4 + 2 / 3) / (Q : ℝ) := by
      dsimp only [resolutionError]
      ring
    _ ≤ ((8 + 33 * Real.log 4 + 2 / 3) * Real.log (Real.log Y)) / (Q : ℝ) :=
      div_le_div_of_nonneg_right hnum hQ0.le
    _ = ((8 + 33 * Real.log 4 + 2 / 3) * Real.log (Real.log Y)) * (1 / (Q : ℝ)) := by ring
    _ ≤ ((8 + 33 * Real.log 4 + 2 / 3) * Real.log (Real.log Y)) *
        (2 * Real.log 16 / Real.log Y) :=
      mul_le_mul_of_nonneg_left hrec (by positivity)
    _ = _ := by dsimp only [profileRateConstant]; ring


/-- An explicit cutoff and rate for every positive starting scale. -/
theorem profile_log_rate {n : ℕ} (hn : profileRateThreshold ≤ (n : ℝ))
    {X : ℝ} (hX : 0 < X) :
    |(∑ a ∈ Finset.range n, fourProfile (X / (3 : ℝ) ^ a)) / (n : ℝ) - 1 / 4| ≤
      profileRateConstant * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ) := by
  have hnR : (1 : ℝ) < n := (rate_scale_bounds hn).1
  have hn1 : 1 ≤ n := by exact_mod_cast (show (0 : ℝ) < n from zero_lt_one.trans hnR)
  obtain ⟨Q, hQ, hcost⟩ := exists_resolution_for_log_rate hn
  calc
    _ ≤ (8 * Real.log (Q : ℝ) + 32 * Real.log 4 + 2 / 3) / (Q : ℝ) +
        (Q : ℝ) * (4 : ℝ) ^ Q * Real.log 4 / (4 * (n : ℝ)) :=
      effective_profile_average hQ hn1 hX
    _ = resolutionError Q + returnCost Q / (n : ℝ) := by
      dsimp only [resolutionError, returnCost]
      ring
    _ ≤ _ := hcost

/-- The profile rate is uniform even when the positive starting scale varies with the orbit length. -/
theorem uniform_profile_log_rate :
    ∃ N : ℕ, ∀ n ≥ N, ∀ X > 0,
      |(∑ a ∈ Finset.range n, fourProfile (X / (3 : ℝ) ^ a)) / (n : ℝ) - 1 / 4| ≤
        profileRateConstant * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ) := by
  obtain ⟨N, hN⟩ := exists_nat_gt profileRateThreshold
  refine ⟨N, ?_⟩
  intro n hn X hX
  exact profile_log_rate (hN.le.trans (Nat.cast_le.mpr hn)) hX

/-- The profile rate constant enlarged by the logarithmic exponent density and floor error. -/
def countRateConstant : ℝ := (1 / Real.log 3 + 1) * profileRateConstant + 7 / 8

theorem countRateConstant_pos : 0 < countRateConstant := by
  have hp : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hC := profileRateConstant_pos
  dsimp only [countRateConstant]
  positivity

private theorem count_cost_log_rate {Y : ℝ} (hY : profileRateThreshold ≤ Y)
    {Q : ℕ} (hQ : 2 ≤ Q)
    (hcost : resolutionError Q + returnCost Q / Y ≤
      profileRateConstant * Real.log (Real.log Y) / Real.log Y) :
    resolutionError Q * (1 / Real.log 3 + 1 / Y) + (returnCost Q + 7 / 8) / Y ≤
      countRateConstant * Real.log (Real.log Y) / Real.log Y := by
  obtain ⟨hy1, _, hloglog⟩ := rate_scale_bounds hY
  have hy0 : 0 < Y := zero_lt_one.trans hy1
  have hL : 0 < Real.log Y := Real.log_pos hy1
  have hp : 0 < Real.log 3 := Real.log_pos (by norm_num)
  let C₃ : ℝ := 1 / Real.log 3 + 1
  have hC₃ : 1 ≤ C₃ := by
    have h := div_nonneg (by norm_num : (0 : ℝ) ≤ 1) hp.le
    dsimp only [C₃]
    linarith only [h]
  have hC₃0 : 0 < C₃ := zero_lt_one.trans_le hC₃
  have hrec : 1 / Y ≤ 1 := (div_le_one hy0).mpr hy1.le
  have hcoef : 1 / Real.log 3 + 1 / Y ≤ C₃ := by dsimp only [C₃]; linarith only [hrec]
  have hR := mul_le_mul_of_nonneg_left hcoef (resolutionError_nonneg hQ)
  have hB : returnCost Q / Y ≤ C₃ * (returnCost Q / Y) := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hC₃
      (div_nonneg (returnCost_nonneg Q) hy0.le)
  have hmain : resolutionError Q * (1 / Real.log 3 + 1 / Y) + (returnCost Q + 7 / 8) / Y ≤
      C₃ * (resolutionError Q + returnCost Q / Y) + 7 / (8 * Y) := by
    have he : (returnCost Q + 7 / 8) / Y = returnCost Q / Y + 7 / (8 * Y) := by ring
    rw [he]
    nlinarith only [hR, hB]
  have hlogY : Real.log Y ≤ Y := by
    have h := Real.log_le_sub_one_of_pos hy0
    linarith only [h]
  have hinv : 1 / Y ≤ Real.log (Real.log Y) / Real.log Y :=
    (div_le_div_of_nonneg_left (by norm_num) hL hlogY).trans
      (div_le_div_of_nonneg_right hloglog hL.le)
  have htail : 7 / (8 * Y) ≤ (7 / 8 : ℝ) * (Real.log (Real.log Y) / Real.log Y) := by
    have h := mul_le_mul_of_nonneg_left hinv (by norm_num : (0 : ℝ) ≤ 7 / 8)
    simpa only [mul_one_div, div_div] using h
  calc
    _ ≤ C₃ * (resolutionError Q + returnCost Q / Y) + 7 / (8 * Y) := hmain
    _ ≤ C₃ * (profileRateConstant * Real.log (Real.log Y) / Real.log Y) +
        (7 / 8 : ℝ) * (Real.log (Real.log Y) / Real.log Y) :=
      add_le_add (mul_le_mul_of_nonneg_left hcost hC₃0.le) htail
    _ = _ := by dsimp only [countRateConstant, C₃]; ring

/-- An explicit iterated-logarithmic rate for the actual integral-count coefficient. -/
theorem integral_count_coefficient_log_rate {X : ℝ}
    (hX : Real.exp profileRateThreshold ≤ X) :
    |(X ^ 2 / 2 - ∫ t in (0 : ℝ)..X, (system.countBall t : ℝ)) / (X * Real.log X) -
      1 / (4 * Real.log 3)| ≤
      countRateConstant * Real.log (Real.log (Real.log X)) / Real.log (Real.log X) := by
  have hx0 : 0 < X := (Real.exp_pos _).trans_le hX
  have hY : profileRateThreshold ≤ Real.log X := by
    have h := Real.log_le_log (Real.exp_pos _) hX
    rwa [Real.log_exp] at h
  have hy1 : 1 < Real.log X := (rate_scale_bounds hY).1
  have hx1 : 1 < X := by
    have h := Real.exp_lt_exp.mpr (zero_lt_one.trans hy1)
    simpa only [Real.exp_zero, Real.exp_log hx0] using h
  obtain ⟨Q, hQ, hcost⟩ := exists_resolution_for_log_rate hY
  exact (effective_integral_count_coefficient_error hQ hx1).trans (count_cost_log_rate hY hQ hcost)

end GaloisForLFunctions.SumProductArithmeticOfTheLogarithm.PositiveNearCount
