import GaloisForLFunctions.RHTower.LiEvenCrossEulerThirdMassRemainder
import GaloisForLFunctions.RHTower.LiEvenCrossEulerFirstNegativeOrder
import GaloisForLFunctions.RHTower.LiEvenCrossEulerSmallMassRemainder

/-!
# The actual Euler jet's three-term crossover profile

The first three source terms become two real exponentials in the offset from
the source-dependent crossover center. The complete later tail is uniformly
`O(v)` on every bounded offset window. Actual jet orders remain natural numbers.
-/

namespace RHTower

noncomputable section

/-- Positive third-source amplitude in the crossover coordinates. -/
def liEvenCrossEulerCrossoverThirdAmplitude : ℝ :=
  9 * normalizedPrimeArchMoment 2 *
    (normalizedPrimeArchMoment 0 / (4 * normalizedPrimeArchMoment 1)) ^
      (Real.log 9 / Real.log 4)

/-- The third source term's small-mass exponent. -/
def liEvenCrossEulerCrossoverExponent : ℝ :=
  2 * liEvenCrossEulerSmallMassHalfExponent

/-- A source model in a real offset variable; the actual jet retains natural order. -/
def liEvenCrossEulerCrossoverTwoExponentialModel (v u : ℝ) : ℝ :=
  normalizedPrimeArchMoment 0 * (1 - (4 : ℝ) ^ u) +
    liEvenCrossEulerCrossoverThirdAmplitude * (9 : ℝ) ^ u *
      v ^ liEvenCrossEulerCrossoverExponent

private theorem crossover_source_ratio_pos :
    0 < normalizedPrimeArchMoment 0 / (4 * normalizedPrimeArchMoment 1) := by
  have h0 := normalizedPrimeArchMoment_pos_of_le_eleven 0 (by omega)
  have h1 := normalizedPrimeArchMoment_pos_of_le_eleven 1 (by omega)
  positivity

theorem liEvenCrossEulerCrossoverThirdAmplitude_pos :
    0 < liEvenCrossEulerCrossoverThirdAmplitude := by
  have h2 := normalizedPrimeArchMoment_pos_of_le_eleven 2 (by omega)
  have hr := Real.rpow_pos_of_pos crossover_source_ratio_pos (Real.log 9 / Real.log 4)
  unfold liEvenCrossEulerCrossoverThirdAmplitude
  positivity

theorem liEvenCrossEulerCrossoverExponent_pos :
    0 < liEvenCrossEulerCrossoverExponent := by
  unfold liEvenCrossEulerCrossoverExponent
  exact mul_pos (by norm_num) liEvenCrossEulerSmallMassHalfExponent_pos

theorem liEvenCrossEulerCrossoverExponent_lt_one_half :
    liEvenCrossEulerCrossoverExponent < 1 / 2 := by
  have h4 := Real.log_pos (by norm_num : (1 : ℝ) < 4)
  have hlog := Real.log_lt_log (by norm_num : (0 : ℝ) < 8) (by norm_num : (8 : ℝ) < 9)
  have h8 : Real.log 8 = 3 * Real.log 2 := by
    simpa only [show (2 : ℝ) ^ (3 : ℕ) = 8 by norm_num, Nat.cast_ofNat] using
      Real.log_pow (2 : ℝ) 3
  have h9 : Real.log 9 = 2 * Real.log 3 := by
    simpa only [show (3 : ℝ) ^ (2 : ℕ) = 9 by norm_num, Nat.cast_ofNat] using
      Real.log_pow (3 : ℝ) 2
  have hfour : Real.log 4 = 2 * Real.log 2 := by
    simpa only [show (2 : ℝ) ^ (2 : ℕ) = 4 by norm_num, Nat.cast_ofNat] using
      Real.log_pow (2 : ℝ) 2
  have hquot : (3 / 4 : ℝ) < Real.log 3 / Real.log 4 := by
    apply (lt_div_iff₀ h4).2
    rw [hfour]
    rw [h8, h9] at hlog
    nlinarith
  dsimp [liEvenCrossEulerCrossoverExponent, liEvenCrossEulerSmallMassHalfExponent]
  linarith

theorem two_mul_liEvenCrossEulerCrossoverExponent_lt_one :
    2 * liEvenCrossEulerCrossoverExponent < 1 := by
  linarith [liEvenCrossEulerCrossoverExponent_lt_one_half]

private theorem crossover_leading_term_eq
    {v : ℝ} (hv : 0 < v) (k : ℕ) :
    (4 : ℝ) ^ (k + 1) * normalizedPrimeArchMoment 1 * v =
      normalizedPrimeArchMoment 0 * (4 : ℝ) ^ ((k : ℝ) - liEvenCrossEulerCrossoverCenter v) := by
  have hb := liEvenCrossEulerCrossoverCenter_rpow_balance hv
  have hx := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 4)
    (liEvenCrossEulerCrossoverCenter v)
  rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 4), Real.rpow_natCast,
    pow_succ, ← mul_div_assoc]
  apply (eq_div_iff hx.ne').2
  calc
    (4 ^ k * 4 * normalizedPrimeArchMoment 1 * v) *
        (4 : ℝ) ^ liEvenCrossEulerCrossoverCenter v =
      4 ^ k * ((4 : ℝ) ^ liEvenCrossEulerCrossoverCenter v *
        (4 * normalizedPrimeArchMoment 1 * v)) := by ring
    _ = 4 ^ k * normalizedPrimeArchMoment 0 := by rw [hb]
    _ = normalizedPrimeArchMoment 0 * 4 ^ k := by ring

/-- The source balance fixes the mass scale exactly in every crossover coordinate. -/
theorem liEvenCrossEulerCrossoverCenter_mass_scale
    {v : ℝ} (hv : 0 < v) (k : ℕ) :
    (4 : ℝ) ^ k * v =
      (normalizedPrimeArchMoment 0 / (4 * normalizedPrimeArchMoment 1)) *
        (4 : ℝ) ^ ((k : ℝ) - liEvenCrossEulerCrossoverCenter v) := by
  have h1 := normalizedPrimeArchMoment_pos_of_le_eleven 1 (by omega)
  have hlead := crossover_leading_term_eq hv k
  rw [pow_succ] at hlead
  field_simp
  nlinarith [hlead]

private theorem crossover_third_mass_scale_eq
    {v : ℝ} (hv : 0 < v) (k : ℕ) :
    (9 : ℝ) ^ k * v ^ 2 =
      (normalizedPrimeArchMoment 0 / (4 * normalizedPrimeArchMoment 1)) ^
        (Real.log 9 / Real.log 4) *
      (9 : ℝ) ^ ((k : ℝ) - liEvenCrossEulerCrossoverCenter v) *
        v ^ liEvenCrossEulerCrossoverExponent := by
  have h9 : (0 : ℝ) < 9 := by norm_num
  have hr := crossover_source_ratio_pos
  have hlog9 : Real.log 9 = 2 * Real.log 3 := by
    simpa only [show (3 : ℝ) ^ (2 : ℕ) = 9 by norm_num, Nat.cast_ofNat] using
      Real.log_pow (3 : ℝ) 2
  apply Real.log_injOn_pos
    (by change (0 : ℝ) < _; positivity) (by change (0 : ℝ) < _; positivity)
  rw [Real.log_mul (pow_pos h9 k).ne' (sq_pos_of_pos hv).ne',
    Real.log_pow, Real.log_pow]
  rw [Real.log_mul (by positivity) (Real.rpow_pos_of_pos hv _).ne',
    Real.log_mul (Real.rpow_pos_of_pos hr _).ne' (Real.rpow_pos_of_pos h9 _).ne',
    Real.log_rpow hr, Real.log_rpow h9, Real.log_rpow hv]
  norm_num only [Nat.cast_ofNat]
  dsimp [liEvenCrossEulerCrossoverCenter, liEvenCrossEulerCrossoverOffset,
    liEvenCrossEulerCrossoverExponent, liEvenCrossEulerSmallMassHalfExponent]
  rw [hlog9]
  ring

private theorem crossover_third_term_eq
    {v : ℝ} (hv : 0 < v) (k : ℕ) :
    (9 : ℝ) ^ (k + 1) * normalizedPrimeArchMoment 2 * v ^ 2 =
      liEvenCrossEulerCrossoverThirdAmplitude *
        (9 : ℝ) ^ ((k : ℝ) - liEvenCrossEulerCrossoverCenter v) *
          v ^ liEvenCrossEulerCrossoverExponent := by
  calc
    (9 : ℝ) ^ (k + 1) * normalizedPrimeArchMoment 2 * v ^ 2 =
      (9 * normalizedPrimeArchMoment 2) * ((9 : ℝ) ^ k * v ^ 2) := by
        rw [pow_succ]
        ring
    _ = _ := by
      rw [crossover_third_mass_scale_eq hv k]
      unfold liEvenCrossEulerCrossoverThirdAmplitude
      ring

/-- Exact actual normalized jet in source crossover coordinates, with its complete later tail. -/
theorem liEvenCrossFirstCurrentEvenEulerJet_eq_crossoverThreeTermProfile
    {v : ℝ} (hv : 0 < v) (hvquarter : v ≤ 1 / 4) (k : ℕ) :
    liEvenCrossFirstCurrentEvenEulerJet v k / (2 * v) =
      liEvenCrossEulerCrossoverTwoExponentialModel v
        ((k : ℝ) - liEvenCrossEulerCrossoverCenter v) + liEvenCrossEulerThirdMassTail v k := by
  rw [liEvenCrossFirstCurrentEvenEulerJet_div_two_mul_mass_eq_three_terms hv hvquarter,
    crossover_leading_term_eq hv, crossover_third_term_eq hv]
  unfold liEvenCrossEulerCrossoverTwoExponentialModel
  ring

/-- A bounded crossover offset bounds `4^k v` independently of mass and order. -/
theorem liEvenCrossEulerCrossoverCenter_mass_scale_le
    {v : ℝ} (hv : 0 < v) (C : ℝ) (k : ℕ)
    (hk : (k : ℝ) - liEvenCrossEulerCrossoverCenter v ≤ C) :
    (4 : ℝ) ^ k * v ≤
      (normalizedPrimeArchMoment 0 / (4 * normalizedPrimeArchMoment 1)) * (4 : ℝ) ^ C := by
  rw [liEvenCrossEulerCrossoverCenter_mass_scale hv]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4) hk)
    crossover_source_ratio_pos.le

/-- Uniform `O(v)` error for the actual jet on every bounded offset window. -/
theorem liEvenCrossEulerCrossoverThreeTermProfile_uniform_remainder (C : ℝ) :
    ∃ D : ℝ, 0 < D ∧
      ∀ᶠ v : ℝ in nhdsWithin 0 (Set.Ioi 0), ∀ k : ℕ,
        |(k : ℝ) - liEvenCrossEulerCrossoverCenter v| ≤ C →
        |liEvenCrossFirstCurrentEvenEulerJet v k / (2 * v) -
          liEvenCrossEulerCrossoverTwoExponentialModel v
            ((k : ℝ) - liEvenCrossEulerCrossoverCenter v)| ≤ D * v := by
  let W : ℝ := (normalizedPrimeArchMoment 0 / (4 * normalizedPrimeArchMoment 1)) *
    (4 : ℝ) ^ C
  let D : ℝ := 32 * xiShiftAbsoluteMass 0 * W ^ 2 / 150 ^ 3 + 1
  have hW : 0 < W := mul_pos crossover_source_ratio_pos
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 4) C)
  have hA := xiShiftAbsoluteMass_nonneg 0
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D, hD, ?_⟩
  have hsmall : (0 : ℝ) < 150 ^ 2 / (64 * W) := by positivity
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 4)).filter_mono nhdsWithin_le_nhds,
    (eventually_lt_nhds hsmall).filter_mono nhdsWithin_le_nhds] with v hv hvquarter hvsmall
  change 0 < v at hv
  intro k hk
  have hw : (4 : ℝ) ^ k * v ≤ W :=
    liEvenCrossEulerCrossoverCenter_mass_scale_le hv C k (le_trans (le_abs_self _) hk)
  have hp0 : 0 ≤ (2 : ℝ) ^ k * v / 150 := by positivity
  have htwo : ((2 : ℝ) ^ k) ^ 2 = (4 : ℝ) ^ k := by
    rw [← pow_mul, Nat.mul_comm k 2, pow_mul]
    norm_num
  have hpsq : ((2 : ℝ) ^ k * v / 150) ^ 2 = ((4 : ℝ) ^ k * v) * v / 150 ^ 2 := by
    rw [div_pow, mul_pow, htwo]
    ring
  have hsmallv : W * v ≤ 150 ^ 2 / 64 := by
    have hh := (lt_div_iff₀ (by positivity : 0 < 64 * W)).mp hvsmall
    nlinarith
  have hpsqle : ((2 : ℝ) ^ k * v / 150) ^ 2 ≤ (1 / 8 : ℝ) ^ 2 := by
    rw [hpsq]
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 150 ^ 2)).2
    nlinarith [mul_le_mul_of_nonneg_right hw hv.le]
  have hp : (2 : ℝ) ^ k * v / 150 ≤ 1 / 8 := by nlinarith
  rw [liEvenCrossFirstCurrentEvenEulerJet_eq_crossoverThreeTermProfile hv hvquarter.le,
    add_sub_cancel_left]
  calc
    |liEvenCrossEulerThirdMassTail v k| ≤
      32 * xiShiftAbsoluteMass 0 * ((4 : ℝ) ^ k * v) ^ 2 * v / 150 ^ 3 :=
        abs_liEvenCrossEulerThirdMassTail_le hv.le k hp
    _ ≤ 32 * xiShiftAbsoluteMass 0 * W ^ 2 * v / 150 ^ 3 := by gcongr
    _ ≤ D * v := by dsimp [D]; nlinarith

end

end RHTower
