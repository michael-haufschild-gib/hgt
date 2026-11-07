import GaloisForLFunctions.SumProductArithmeticOfTheLogarithm.ComplementaryRotationAverages
import GaloisForLFunctions.SumProductArithmeticOfTheLogarithm.PositiveNearCountProfileBridge
import GaloisForLFunctions.BiScaleUncertainty.PrimePowerDeletionPairThreshold

/-!
# Exact logarithmic coefficient of the averaged count deficit

For the positive odd-prime model with extra norms three and four, the first
count deficit divided by `x log x` tends to `1 / (4 log 3)`.

The norm-four profile becomes a continuous function on the circle of length
`log 4`. Its complementary half-period identity fixes the uniform average
along rotation by `log 3` at one quarter. Integer prime-power independence
makes this rotation dense. The actual count-profile error is bounded, so the
uniform average and the logarithmic exponent count give the stated limit.
-/

noncomputable section
open scoped BigOperators Classical
namespace GaloisForLFunctions.SumProductArithmeticOfTheLogarithm.PositiveNearCount

/-- The multiplicatively periodic count profile in logarithmic coordinates. -/
def logarithmicProfile (t : ℝ) : ℝ := fourProfile (Real.exp t)

theorem continuous_logarithmicProfile : Continuous logarithmicProfile := by
  apply continuous_iff_continuousAt.mpr
  intro t
  exact (continuousAt_fourProfile (Real.exp_pos t)).comp Real.continuous_exp.continuousAt

theorem logarithmicProfile_periodic : Function.Periodic logarithmicProfile (Real.log 4) := by
  intro t
  change fourProfile (Real.exp (t + Real.log 4)) = fourProfile (Real.exp t)
  rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 4),
    show Real.exp t * 4 = 4 * Real.exp t by ring]
  exact fourProfile_four (Real.exp_pos t)

private theorem log_four_half : Real.log 4 / 2 = Real.log 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  norm_num

private theorem logarithmicProfile_half (t : ℝ) :
    logarithmicProfile t + logarithmicProfile (t - Real.log 4 / 2) = 1 / 2 := by
  rw [log_four_half]
  dsimp only [logarithmicProfile]
  rw [Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  exact fourProfile_half (Real.exp_pos t)

private theorem irrational_three_four : Irrational (Real.log 3 / Real.log 4) := by
  have h := BiScaleUncertainty.irrational_log_div_log
    (p := 3) (q := 2) (a := 1) (b := 2)
    (by norm_num) Nat.prime_two (by norm_num) (by norm_num) (by norm_num)
  norm_num at h
  exact h

private abbrev profileCircle := AddCircle (Real.log 4)

private def circleProfile : C(profileCircle, ℝ) where
  toFun := logarithmicProfile_periodic.lift
  continuous_toFun := by
    unfold Function.Periodic.lift
    exact continuous_logarithmicProfile.quotient_liftOn' _

private theorem circleProfile_coe (t : ℝ) :
    circleProfile (t : profileCircle) = logarithmicProfile t := rfl

private theorem circle_half_involution :
    ((Real.log 4 / 2 : ℝ) : profileCircle) + ((Real.log 4 / 2 : ℝ) : profileCircle) = 0 := by
  rw [← AddCircle.coe_add, show Real.log 4 / 2 + Real.log 4 / 2 = Real.log 4 by ring,
    AddCircle.coe_period]

private theorem circleProfile_half (x : profileCircle) :
    circleProfile x + circleProfile (x - ((Real.log 4 / 2 : ℝ) : profileCircle)) = 1 / 2 := by
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective x
  rw [← AddCircle.coe_sub, circleProfile_coe, circleProfile_coe]
  exact logarithmicProfile_half t

private theorem circle_three_dense :
    DenseRange (fun k : ℤ => k • ((Real.log 3 : ℝ) : profileCircle)) :=
  AddCircle.denseRange_zsmul_coe_iff.mpr irrational_three_four

private theorem circleProfile_orbit {X : ℝ} (hX : 0 < X) (i : ℕ) :
    circleProfile (((Real.log X : ℝ) : profileCircle) -
      i • ((Real.log 3 : ℝ) : profileCircle)) = fourProfile (X / (3 : ℝ) ^ i) := by
  rw [← AddCircle.coe_nsmul, ← AddCircle.coe_sub, circleProfile_coe]
  change fourProfile (Real.exp (Real.log X - i • Real.log 3)) = _
  rw [nsmul_eq_mul, Real.exp_sub, Real.exp_log hX, Real.exp_nat_mul,
    Real.exp_log (by norm_num : (0 : ℝ) < 3)]

/-- Profile averages converge uniformly even when the starting scale varies. -/
theorem uniform_profile_average :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ X > 0,
      |(∑ a ∈ Finset.range n, fourProfile (X / (3 : ℝ) ^ a)) / (n : ℝ) - 1 / 4| < ε := by
  letI : Fact (0 < Real.log 4) := ⟨Real.log_pos (by norm_num)⟩
  intro ε hε
  obtain ⟨N, hN⟩ := uniform_rotation_average_of_complement circleProfile
    circle_three_dense circle_half_involution circleProfile_half ε hε
  refine ⟨N, ?_⟩
  intro n hn X hX
  have h := hN n hn ((Real.log X : ℝ) : profileCircle)
  simpa only [rotationSum, circleProfile_orbit hX,
    show (1 / 2 : ℝ) / 2 = 1 / 4 by norm_num] using h

private theorem floor_length_ratio {L d : ℝ} (hL : 0 < L) (hd : 0 < d) :
    0 ≤ ((⌊L / d⌋₊ + 1 : ℕ) : ℝ) / L - 1 / d ∧
      ((⌊L / d⌋₊ + 1 : ℕ) : ℝ) / L - 1 / d ≤ 1 / L := by
  have hlo := Nat.floor_le (div_pos hL hd).le
  have hhi := (Nat.lt_floor_add_one (L / d)).le
  constructor
  · apply sub_nonneg.mpr
    apply (le_div_iff₀ hL).mpr
    convert hhi using 1 <;> push_cast <;> ring
  · have hn : ((⌊L / d⌋₊ + 1 : ℕ) : ℝ) ≤ L / d + 1 := by
      push_cast
      linarith only [hlo]
    have hdiv := div_le_div_of_nonneg_right hn hL.le
    have he : (L / d + 1) / L = 1 / d + 1 / L := by
      field_simp
    rw [he] at hdiv
    linarith only [hdiv]

private theorem scaled_average_error {D S n L d η : ℝ}
    (hn : 0 < n) (hL : 0 < L) (hd : 0 < d)
    (hD : |D - S| ≤ 5 / 8) (hS : |S / n - 1 / 4| ≤ η)
    (hr : 0 ≤ n / L - 1 / d ∧ n / L - 1 / d ≤ 1 / L) :
    |D / L - 1 / (4 * d)| ≤ η * (n / L) + 7 / (8 * L) := by
  have he : D / L - 1 / (4 * d) =
      (D - S) / L + (S / n - 1 / 4) * (n / L) + (n / L - 1 / d) / 4 := by
    field_simp
    ring
  have he1 : |(D - S) / L| ≤ (5 / 8) / L := by
    rw [abs_div, abs_of_pos hL]
    exact div_le_div_of_nonneg_right hD hL.le
  have he2 : |(S / n - 1 / 4) * (n / L)| ≤ η * (n / L) := by
    rw [abs_mul, abs_of_pos (div_pos hn hL)]
    exact mul_le_mul_of_nonneg_right hS (div_pos hn hL).le
  have he3 : |(n / L - 1 / d) / 4| ≤ (1 / L) / 4 := by
    rw [abs_div, abs_of_nonneg hr.1]
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    exact div_le_div_of_nonneg_right hr.2 (by norm_num)
  calc
    _ = |(D - S) / L + (S / n - 1 / 4) * (n / L) + (n / L - 1 / d) / 4| := by rw [he]
    _ ≤ (|(D - S) / L| + |(S / n - 1 / 4) * (n / L)|) + |(n / L - 1 / d) / 4| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ ((5 / 8) / L + η * (n / L)) + (1 / L) / 4 :=
      add_le_add (add_le_add he1 he2) he3
    _ = _ := by ring

private theorem log_three_power_cutoffs {X : ℝ} (hX : 1 ≤ X) :
    (3 : ℝ) ^ ⌊Real.log X / Real.log 3⌋₊ ≤ X ∧
      X < (3 : ℝ) ^ (⌊Real.log X / Real.log 3⌋₊ + 1) := by
  have hx : 0 < X := zero_lt_one.trans_le hX
  have hd : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hr : 0 ≤ Real.log X / Real.log 3 := div_nonneg (Real.log_nonneg hX) hd.le
  have hlo := Nat.floor_le hr
  have hhi := Nat.lt_floor_add_one (Real.log X / Real.log 3)
  constructor
  · apply (Real.log_le_log_iff (pow_pos (by norm_num : (0 : ℝ) < 3) _) hx).mp
    rw [Real.log_pow]
    exact (le_div_iff₀ hd).mp hlo
  · apply (Real.log_lt_log_iff hx (pow_pos (by norm_num : (0 : ℝ) < 3) _)).mp
    rw [Real.log_pow]
    push_cast
    exact (div_lt_iff₀ hd).mp hhi

/-- The actual first count average has exact leading deficit coefficient `1/(4 log 3)`. -/
theorem riesz_deficit_converges :
    ∀ ε > 0, ∃ X₀ : ℝ, ∀ X ≥ X₀,
      |(X ^ 2 / 2 - rieszCount X) / (X * Real.log X) - 1 / (4 * Real.log 3)| < ε := by
  intro ε hε
  have hd : 0 < Real.log 3 := Real.log_pos (by norm_num)
  let C : ℝ := 1 / Real.log 3 + 1
  have hC : 0 < C := by dsimp only [C]; positivity
  let η : ℝ := ε / (2 * C)
  have hη : 0 < η := by dsimp only [η]; positivity
  obtain ⟨N, hN⟩ := uniform_profile_average η hη
  refine ⟨Real.exp (1 + (N : ℝ) * Real.log 3 + 7 / (4 * ε)), ?_⟩
  intro X hX
  have hX0 : 0 < X := (Real.exp_pos _).trans_le hX
  have hNprod : 0 ≤ (N : ℝ) * Real.log 3 := mul_nonneg (Nat.cast_nonneg _) hd.le
  have htpos : 0 < 7 / (4 * ε) := by positivity
  have hX1 : 1 ≤ X := by
    have ht : 0 ≤ 1 + (N : ℝ) * Real.log 3 + 7 / (4 * ε) := by positivity
    have h := (Real.exp_le_exp.mpr ht).trans hX
    simpa only [Real.exp_zero] using h
  let L := Real.log X
  have hL : 1 + (N : ℝ) * Real.log 3 + 7 / (4 * ε) ≤ L := by
    have h := Real.log_le_log (Real.exp_pos _) hX
    rwa [Real.log_exp] at h
  have hL1 : 1 ≤ L := by linarith only [hL, hNprod, htpos]
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hLN : (N : ℝ) * Real.log 3 ≤ L := by linarith only [hL, htpos]
  let A := ⌊L / Real.log 3⌋₊
  have hNlen : N ≤ A + 1 := by
    have hr : (N : ℝ) ≤ L / Real.log 3 := (le_div_iff₀ hd).mpr hLN
    have hh : (N : ℝ) < (A : ℝ) + 1 := hr.trans_lt (Nat.lt_floor_add_one _)
    exact_mod_cast hh.le
  have hn : 0 < ((A + 1 : ℕ) : ℝ) := by positivity
  have hAvg := hN (A + 1) hNlen X hX0
  have hp := log_three_power_cutoffs hX1
  have hErr := normalized_deficit_profile_error hX1 A hp.1 hp.2
  have hr := floor_length_ratio hL0 hd
  have hScale := scaled_average_error hn hL0 hd hErr hAvg.le hr
  have hrec : 1 / L ≤ 1 := (div_le_one hL0).mpr hL1
  have hcap : ((A + 1 : ℕ) : ℝ) / L ≤ C := by
    dsimp only [C]
    linarith only [hr.2, hrec]
  have hηcap : η * (((A + 1 : ℕ) : ℝ) / L) ≤ ε / 2 := by
    calc
      _ ≤ η * C := mul_le_mul_of_nonneg_left hcap hη.le
      _ = ε / 2 := by dsimp only [η]; field_simp
  have hcrit : 7 / (4 * ε) < L := by linarith only [hL, hNprod]
  have hcrit' := (div_lt_iff₀ (by positivity : 0 < 4 * ε)).mp hcrit
  have htail : 7 / (8 * L) < ε / 2 := by
    apply (div_lt_iff₀ (by positivity : 0 < 8 * L)).mpr
    nlinarith only [hcrit']
  have hfinal := lt_of_le_of_lt hScale
    (show η * (((A + 1 : ℕ) : ℝ) / L) + 7 / (8 * L) < ε by
      linarith only [hηcap, htail])
  simpa only [L, div_div] using hfinal

/-- The normalized first count deficit tends to its exact logarithmic coefficient. -/
theorem tendsto_riesz_deficit :
    Filter.Tendsto (fun X : ℝ => (X ^ 2 / 2 - rieszCount X) / (X * Real.log X))
      Filter.atTop (nhds (1 / (4 * Real.log 3))) := by
  apply Metric.tendsto_atTop.mpr
  simpa only [Real.dist_eq] using riesz_deficit_converges

/-- The same coefficient governs the integral of the actual generalized-integer count. -/
theorem tendsto_integral_count_deficit :
    Filter.Tendsto
      (fun X : ℝ => (X ^ 2 / 2 - ∫ t in (0 : ℝ)..X, (system.countBall t : ℝ)) /
        (X * Real.log X)) Filter.atTop (nhds (1 / (4 * Real.log 3))) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨X₀, hX₀⟩ := riesz_deficit_converges ε hε
  refine ⟨max 0 X₀, ?_⟩
  intro X hX
  have hX0 : 0 ≤ X := (le_max_left 0 X₀).trans hX
  rw [Real.dist_eq, ← rieszCount_eq_integral_count hX0]
  exact hX₀ X ((le_max_right 0 X₀).trans hX)

end GaloisForLFunctions.SumProductArithmeticOfTheLogarithm.PositiveNearCount
