import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.GrowingConductorsHaveUniformReciprocalShellRates
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.CountingActiveShellsMakesTheAffineSourceLinear
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheUpwardPrimeRowsRealizeTheCompletedShellCorrection
import GaloisForLFunctions.HTGeometry.HarmonicQuotientTailBound

/-!
# Uniform harmonic source bounds for growing conductor families

Split the actual affine shell source at complementary quotient
`2c exp(sqrt(log N))`. Signed residue cancellation pays the large quotients;
the uniform linear source bound pays the remaining harmonic mass.
One constant works for every logarithmic conductor range and both orientations.
-/

noncomputable section
open MeasureTheory Filter Topology Finset
namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open RenormalizedArithmeticPotentialTheory SpacingScaleHarmonicAnalysis
  BezoutValuationIncidence RenormalizedArithmeticPotentialTheory.CompletedShell

/-- A logarithmically growing conductor family shares one harmonic error constant.
The complementary-quotient split retains the full affine source and every shift. -/
theorem exists_conductor_uniform_shiftedReciprocal_harmonic_bound
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ A : ℝ, 0 ≤ A → ∀ᶠ N : ℕ in atTop,
      ∀ m : ℕ, 0 < m → (m : ℝ) ≤ Real.log (N : ℝ) ^ A →
      ∀ c : ℝ, 1 ≤ c → ∀ shift : ℕ → ℕ,
        (∑ n ∈ Icc 1 N, shiftedReciprocalUpwardRowError φ c shift N m n ^ 2) /
          Real.log N ≤ K * (m.totient : ℝ) ^ 2 * c ^ 3 / Real.sqrt (Real.log N) := by
  obtain ⟨C, hC, hsource⟩ :=
    exists_conductor_uniform_affineShellCorrection_linear_log_rate hφ hsupp hM
  let D : ℝ := 4 * (Real.log 4 + 4)
  have hD : 0 ≤ D := by
    have hlog := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
    dsimp only [D]
    positivity
  let K := 2 * C ^ 2 + 5 * D ^ 2
  refine ⟨K, by dsimp only [K]; positivity, ?_⟩
  intro A hA
  have hloglim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hYlim : Tendsto (fun N : ℕ => Real.exp (Real.sqrt (Real.log N))) atTop atTop :=
    Real.tendsto_exp_atTop.comp (Real.tendsto_sqrt_atTop.comp hloglim)
  filter_upwards [hYlim.eventually (hsource (2 * A) (by positivity) 2),
    hloglim.eventually_ge_atTop 1, eventually_ge_atTop 1] with N hsourceN hL hN
  intro m hm hmN c hc shift
  let L := Real.log (N : ℝ)
  let Y := Real.exp (Real.sqrt L)
  let T := 2 * c * Y
  let a := C * c / L
  let b := D * (m.totient : ℝ) * c
  have hL1 : 1 ≤ L := hL
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have htot : (1 : ℝ) ≤ m.totient := by
    exact_mod_cast Nat.totient_pos.mpr hm
  have htot2 : (1 : ℝ) ≤ (m.totient : ℝ) ^ 2 := one_le_pow₀ htot
  have hc3 : c ^ 2 ≤ c ^ 3 := pow_le_pow_right₀ hc (by norm_num)
  have hs1 : 1 ≤ Real.sqrt L := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hL1
  have hs0 : 0 < Real.sqrt L := zero_lt_one.trans_le hs1
  have hY1 : 1 ≤ Y := Real.one_le_exp_iff.mpr (Real.sqrt_nonneg _)
  have hT : 1 ≤ T := by dsimp only [T]; nlinarith only [hc, hY1]
  have hmY : (m : ℝ) ≤ Real.log Y ^ (2 * A) := by
    dsimp only [Y]
    rw [Real.log_exp]
    have heq : L ^ A = Real.sqrt L ^ (2 * A) := by
      convert Real.rpow_div_two_eq_sqrt (2 * A) hL0.le using 1 <;> ring
    exact hmN.trans_eq heq
  have hglobal : ∀ n ∈ Icc 1 N,
      |shiftedReciprocalUpwardRowError φ c shift N m n| ≤ b / Real.sqrt n := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    have hnN : (n : ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp hn).2
    have hquot : 1 ≤ (N : ℝ) / n := (le_div_iff₀ hn0).mpr
      (by simpa only [one_mul] using hnN)
    rw [shiftedReciprocalUpwardRowError, abs_div, abs_of_nonneg (Real.sqrt_nonneg n)]
    exact div_le_div_of_nonneg_right
      (abs_affineShellCorrection_error_le_linear hm hφ hsupp hM n shift hc0 hquot)
      (Real.sqrt_nonneg _)
  have hgood : ∀ n ∈ Icc 1 N, T ≤ (N : ℝ) / n →
      |shiftedReciprocalUpwardRowError φ c shift N m n| ≤ a / Real.sqrt n := by
    intro n _ ht
    have hb := hsourceN.2 m hm hmY c ((N : ℝ) / n) hc ht shift n
    rw [Real.log_exp, Real.sq_sqrt (Real.log_natCast_nonneg N)] at hb
    rw [shiftedReciprocalUpwardRowError, abs_div, abs_of_nonneg (Real.sqrt_nonneg n)]
    exact div_le_div_of_nonneg_right hb (Real.sqrt_nonneg _)
  have hsum := HTGeometry.sum_sq_le_harmonic_quotient_tail hN hT
    (shiftedReciprocalUpwardRowError φ c shift N m) hglobal hgood
  have hhead : a ^ 2 * (1 + L) ≤
      2 * C ^ 2 * (m.totient : ℝ) ^ 2 * c ^ 3 * Real.sqrt L := by
    have hfrac : (1 + L) / L ^ 2 ≤ 2 := by
      apply (div_le_iff₀ (sq_pos_of_pos hL0)).mpr
      nlinarith only [hL1]
    have hmass : c ^ 2 ≤ (m.totient : ℝ) ^ 2 * c ^ 3 := by
      exact hc3.trans (by simpa only [one_mul] using
        mul_le_mul_of_nonneg_right htot2 (pow_nonneg hc0.le 3))
    calc
      _ = C ^ 2 * c ^ 2 * ((1 + L) / L ^ 2) := by dsimp only [a]; ring
      _ ≤ 2 * C ^ 2 * c ^ 2 := by
        have h := mul_le_mul_of_nonneg_left hfrac (show 0 ≤ C ^ 2 * c ^ 2 by positivity)
        nlinarith only [h]
      _ ≤ 2 * C ^ 2 * ((m.totient : ℝ) ^ 2 * c ^ 3) :=
        mul_le_mul_of_nonneg_left hmass (by positivity)
      _ ≤ _ := by
        have h := mul_le_mul_of_nonneg_left hs1
          (show 0 ≤ 2 * C ^ 2 * (m.totient : ℝ) ^ 2 * c ^ 3 by positivity)
        simpa only [mul_one, mul_assoc] using h
  have hlogT : 1 + Real.log (2 * T) ≤ 4 * c + Real.sqrt L := by
    have hid : 2 * T = (4 * c) * Real.exp (Real.sqrt L) := by dsimp only [T, Y]; ring
    rw [hid, Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp]
    have hb := Real.log_le_sub_one_of_pos (show 0 < 4 * c by positivity)
    linarith only [hb]
  have htail : b ^ 2 * (1 + Real.log (2 * T)) ≤
      5 * D ^ 2 * (m.totient : ℝ) ^ 2 * c ^ 3 * Real.sqrt L := by
    have hcs : 4 * c + Real.sqrt L ≤ 5 * c * Real.sqrt L := by
      have h1 := mul_le_mul_of_nonneg_left hs1 (show 0 ≤ 4 * c by positivity)
      have h2 := mul_le_mul_of_nonneg_right hc hs0.le
      nlinarith only [h1, h2]
    calc
      _ ≤ b ^ 2 * (4 * c + Real.sqrt L) := mul_le_mul_of_nonneg_left hlogT (sq_nonneg _)
      _ ≤ b ^ 2 * (5 * c * Real.sqrt L) := mul_le_mul_of_nonneg_left hcs (sq_nonneg _)
      _ = _ := by dsimp only [b]; ring
  have hraw : (∑ n ∈ Icc 1 N, shiftedReciprocalUpwardRowError φ c shift N m n ^ 2) ≤
      K * (m.totient : ℝ) ^ 2 * c ^ 3 * Real.sqrt L := by
    have hb := hsum.trans (add_le_add hhead htail)
    dsimp only [K]
    nlinarith only [hb]
  change _ / L ≤ K * (m.totient : ℝ) ^ 2 * c ^ 3 / Real.sqrt L
  calc
    _ ≤ (K * (m.totient : ℝ) ^ 2 * c ^ 3 * Real.sqrt L) / L :=
      div_le_div_of_nonneg_right hraw hL0.le
    _ = (K * (m.totient : ℝ) ^ 2 * c ^ 3 * Real.sqrt L) / (Real.sqrt L) ^ 2 := by
      rw [Real.sq_sqrt hL0.le]
    _ = _ := by field_simp

#print axioms exists_conductor_uniform_shiftedReciprocal_harmonic_bound

/-- The two signed reciprocal orientations obey the same uniform conductor bound. -/
theorem exists_conductor_uniform_reciprocalUpward_harmonic_bound
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ A : ℝ, 0 ≤ A → ∀ᶠ N : ℕ in atTop,
      ∀ m : ℕ, 0 < m → (m : ℝ) ≤ Real.log (N : ℝ) ^ A →
      ∀ c : ℝ, 1 ≤ c → ∀ B : ℕ, ⌈c⌉₊ ≤ B →
        (∑ n ∈ Icc 1 N,
          ((reciprocalUpwardCoefficient φ c B N m n -
            ramanujanLagCoefficient m n * shellCorrection φ c m) / Real.sqrt n) ^ 2) /
          Real.log N ≤ K * (m.totient : ℝ) ^ 2 * c ^ 3 / Real.sqrt (Real.log N) := by
  obtain ⟨K, hK, hbound⟩ :=
    exists_conductor_uniform_shiftedReciprocal_harmonic_bound hφ hsupp hM
  refine ⟨K, hK, fun A hA => ?_⟩
  filter_upwards [hbound A hA] with N hN
  intro m hm hmN c hc B hB
  have hc0 := zero_lt_one.trans_le hc
  have hrow (n : ℕ) (hn : 1 ≤ n) :
      (reciprocalUpwardCoefficient φ c B N m n -
        ramanujanLagCoefficient m n * shellCorrection φ c m) / Real.sqrt n =
      (shiftedReciprocalUpwardRowError φ c id N m n +
        shiftedReciprocalUpwardRowError φ c (reflectedAffineShift m) N m n) / 2 := by
    rw [reciprocalUpwardCoefficient_eq_shifted_corrections hφ hsupp hc0 hB N m n hn]
    dsimp only [shiftedReciprocalUpwardRowError]
    rw [shellCorrectionOfShift_reflected hm]
    change _ = ((affinePrimeShellCorrectionOfShift m n id φ c ((N : ℝ) / n) -
      ramanujanLagCoefficient m n * shellCorrection φ c m) / Real.sqrt n + _) / 2
    ring
  have hsum : (∑ n ∈ Icc 1 N,
      ((reciprocalUpwardCoefficient φ c B N m n -
        ramanujanLagCoefficient m n * shellCorrection φ c m) / Real.sqrt n) ^ 2) ≤
      ∑ n ∈ Icc 1 N, (shiftedReciprocalUpwardRowError φ c id N m n ^ 2 +
        shiftedReciprocalUpwardRowError φ c (reflectedAffineShift m) N m n ^ 2) / 2 := by
    apply sum_le_sum
    intro n hn
    rw [hrow n (mem_Icc.mp hn).1]
    nlinarith only [sq_nonneg (shiftedReciprocalUpwardRowError φ c id N m n -
      shiftedReciprocalUpwardRowError φ c (reflectedAffineShift m) N m n)]
  have hfinal := div_le_div_of_nonneg_right hsum (Real.log_natCast_nonneg N)
  rw [← sum_div, sum_add_distrib, div_right_comm, add_div] at hfinal
  have hp := hN m hm hmN c hc id
  have hn := hN m hm hmN c hc (reflectedAffineShift m)
  linarith only [hfinal, hp, hn]

/-- The explicit tilted spline has one source-error constant for every logarithmic conductor range. -/
theorem exists_tiltedUnitSpline_conductor_uniform_reciprocalUpward_harmonic_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ A : ℝ, 0 ≤ A → ∀ᶠ N : ℕ in atTop,
      ∀ m : ℕ, 0 < m → (m : ℝ) ≤ Real.log (N : ℝ) ^ A →
      ∀ c : ℝ, 1 ≤ c → ∀ B : ℕ, ⌈c⌉₊ ≤ B →
        (∑ n ∈ Icc 1 N,
          ((reciprocalUpwardCoefficient tiltedUnitSpline c B N m n -
            ramanujanLagCoefficient m n * shellCorrection tiltedUnitSpline c m) / Real.sqrt n) ^ 2) /
          Real.log N ≤ K * (m.totient : ℝ) ^ 2 * c ^ 3 / Real.sqrt (Real.log N) :=
  exists_conductor_uniform_reciprocalUpward_harmonic_bound contDiff_tiltedUnitSpline
    tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos

#print axioms exists_conductor_uniform_reciprocalUpward_harmonic_bound
#print axioms exists_tiltedUnitSpline_conductor_uniform_reciprocalUpward_harmonic_bound

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
