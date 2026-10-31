import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.CompleteConductorResidualsAreUniformOnLogarithmicFamilies

/-!
# Conductor residuals with a free logarithmic cutoff

Split quotient horizons at `exp((log N)^(1/k))`. Arbitrarily high reciprocal
shell rates then give a normalized source error of order `(log N)^(1/k-1)`.
The exact eight-term decomposition retains that rate in the complete Weil
residual, uniformly over every fixed logarithmic conductor range.
-/

set_option autoImplicit false

noncomputable section
open MeasureTheory Filter Topology Finset
open scoped RealInnerProductSpace
namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open RenormalizedArithmeticPotentialTheory SpacingScaleHarmonicAnalysis
  BezoutValuationIncidence ArithmeticElectrostatics
  RenormalizedArithmeticPotentialTheory.CompletedShell

/-- A logarithmically growing conductor family shares one harmonic error constant.
The complementary-quotient split retains the full affine source and every shift. -/
theorem exists_conductor_uniform_shiftedReciprocal_variable_rate
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ A : ℝ, 0 ≤ A → ∀ k : ℕ, 1 ≤ k → ∀ᶠ N : ℕ in atTop,
      ∀ m : ℕ, 0 < m → (m : ℝ) ≤ Real.log (N : ℝ) ^ A →
      ∀ c : ℝ, 1 ≤ c → ∀ shift : ℕ → ℕ,
        (∑ n ∈ Icc 1 N, shiftedReciprocalUpwardRowError φ c shift N m n ^ 2) /
          Real.log N ≤ K * (m.totient : ℝ) ^ 2 * c ^ 3 * Real.log N ^ (1 / (k : ℝ)) / Real.log N := by
  obtain ⟨C, hC, hsource⟩ :=
    exists_conductor_uniform_affineShellCorrection_linear_log_rate hφ hsupp hM
  let D : ℝ := 4 * (Real.log 4 + 4)
  have hD : 0 ≤ D := by
    have hlog := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
    dsimp only [D]
    positivity
  let K := 2 * C ^ 2 + 5 * D ^ 2
  refine ⟨K, by dsimp only [K]; positivity, ?_⟩
  intro A hA k hk
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hloglim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hYlim : Tendsto (fun N : ℕ => Real.exp (Real.log N ^ (1 / (k : ℝ)))) atTop atTop :=
    Real.tendsto_exp_atTop.comp ((tendsto_rpow_atTop (by positivity : (0 : ℝ) < 1 / (k : ℝ))).comp hloglim)
  filter_upwards [hYlim.eventually (hsource (A * k) (by positivity) k),
    hloglim.eventually_ge_atTop 1, eventually_ge_atTop 1] with N hsourceN hL hN
  intro m hm hmN c hc shift
  let L := Real.log (N : ℝ)
  let Y := Real.exp (L ^ (1 / (k : ℝ)))
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
  have hs1 : 1 ≤ L ^ (1 / (k : ℝ)) := Real.one_le_rpow hL1 (by positivity)
  have hs0 : 0 < L ^ (1 / (k : ℝ)) := Real.rpow_pos_of_pos hL0 _
  have hsPow : (L ^ (1 / (k : ℝ))) ^ k = L := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le,
      one_div_mul_cancel hkR.ne', Real.rpow_one]
  have hY1 : 1 ≤ Y := Real.one_le_exp_iff.mpr hs0.le
  have hT : 1 ≤ T := by dsimp only [T]; nlinarith only [hc, hY1]
  have hmY : (m : ℝ) ≤ Real.log Y ^ (A * k) := by
    dsimp only [Y]
    rw [Real.log_exp, ← Real.rpow_mul hL0.le]
    have heq : (1 / (k : ℝ)) * (A * k) = A := by field_simp [hkR.ne']
    rw [heq]
    exact hmN
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
    change |affinePrimeShellCorrectionOfShift m n shift φ c ((N : ℝ) / n) -
      ramanujanLagCoefficient m n * shellCorrectionOfShift φ c m shift| ≤
        C * c / Real.log Y ^ k at hb
    rw [show Real.log Y = L ^ (1 / (k : ℝ)) by exact Real.log_exp _, hsPow] at hb
    rw [shiftedReciprocalUpwardRowError, abs_div, abs_of_nonneg (Real.sqrt_nonneg n)]
    exact div_le_div_of_nonneg_right hb (Real.sqrt_nonneg _)
  have hsum := HTGeometry.sum_sq_le_harmonic_quotient_tail hN hT
    (shiftedReciprocalUpwardRowError φ c shift N m) hglobal hgood
  have hhead : a ^ 2 * (1 + L) ≤
      2 * C ^ 2 * (m.totient : ℝ) ^ 2 * c ^ 3 * (L ^ (1 / (k : ℝ))) := by
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
  have hlogT : 1 + Real.log (2 * T) ≤ 4 * c + (L ^ (1 / (k : ℝ))) := by
    have hid : 2 * T = (4 * c) * Real.exp (L ^ (1 / (k : ℝ))) := by dsimp only [T, Y]; ring
    rw [hid, Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp]
    have hb := Real.log_le_sub_one_of_pos (show 0 < 4 * c by positivity)
    linarith only [hb]
  have htail : b ^ 2 * (1 + Real.log (2 * T)) ≤
      5 * D ^ 2 * (m.totient : ℝ) ^ 2 * c ^ 3 * (L ^ (1 / (k : ℝ))) := by
    have hcs : 4 * c + (L ^ (1 / (k : ℝ))) ≤ 5 * c * (L ^ (1 / (k : ℝ))) := by
      have h1 := mul_le_mul_of_nonneg_left hs1 (show 0 ≤ 4 * c by positivity)
      have h2 := mul_le_mul_of_nonneg_right hc hs0.le
      nlinarith only [h1, h2]
    calc
      _ ≤ b ^ 2 * (4 * c + (L ^ (1 / (k : ℝ)))) := mul_le_mul_of_nonneg_left hlogT (sq_nonneg _)
      _ ≤ b ^ 2 * (5 * c * (L ^ (1 / (k : ℝ)))) := mul_le_mul_of_nonneg_left hcs (sq_nonneg _)
      _ = _ := by dsimp only [b]; ring
  have hraw : (∑ n ∈ Icc 1 N, shiftedReciprocalUpwardRowError φ c shift N m n ^ 2) ≤
      K * (m.totient : ℝ) ^ 2 * c ^ 3 * (L ^ (1 / (k : ℝ))) := by
    have hb := hsum.trans (add_le_add hhead htail)
    dsimp only [K]
    nlinarith only [hb]
  exact div_le_div_of_nonneg_right hraw hL0.le

#print axioms exists_conductor_uniform_shiftedReciprocal_variable_rate

/-- The two signed reciprocal orientations obey the same uniform conductor bound. -/
theorem exists_conductor_uniform_reciprocalUpward_variable_rate
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ A : ℝ, 0 ≤ A → ∀ k : ℕ, 1 ≤ k → ∀ᶠ N : ℕ in atTop,
      ∀ m : ℕ, 0 < m → (m : ℝ) ≤ Real.log (N : ℝ) ^ A →
      ∀ c : ℝ, 1 ≤ c → ∀ B : ℕ, ⌈c⌉₊ ≤ B →
        (∑ n ∈ Icc 1 N,
          ((reciprocalUpwardCoefficient φ c B N m n -
            ramanujanLagCoefficient m n * shellCorrection φ c m) / Real.sqrt n) ^ 2) /
          Real.log N ≤ K * (m.totient : ℝ) ^ 2 * c ^ 3 * Real.log N ^ (1 / (k : ℝ)) / Real.log N := by
  obtain ⟨K, hK, hbound⟩ :=
    exists_conductor_uniform_shiftedReciprocal_variable_rate hφ hsupp hM
  refine ⟨K, hK, fun A hA k hk => ?_⟩
  filter_upwards [hbound A hA k hk] with N hN
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
theorem exists_tiltedUnitSpline_conductor_uniform_reciprocalUpward_variable_rate :
    ∃ K : ℝ, 0 < K ∧ ∀ A : ℝ, 0 ≤ A → ∀ k : ℕ, 1 ≤ k → ∀ᶠ N : ℕ in atTop,
      ∀ m : ℕ, 0 < m → (m : ℝ) ≤ Real.log (N : ℝ) ^ A →
      ∀ c : ℝ, 1 ≤ c → ∀ B : ℕ, ⌈c⌉₊ ≤ B →
        (∑ n ∈ Icc 1 N,
          ((reciprocalUpwardCoefficient tiltedUnitSpline c B N m n -
            ramanujanLagCoefficient m n * shellCorrection tiltedUnitSpline c m) / Real.sqrt n) ^ 2) /
          Real.log N ≤ K * (m.totient : ℝ) ^ 2 * c ^ 3 * Real.log N ^ (1 / (k : ℝ)) / Real.log N :=
  exists_conductor_uniform_reciprocalUpward_variable_rate contDiff_tiltedUnitSpline
    tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos

#print axioms exists_conductor_uniform_reciprocalUpward_variable_rate
#print axioms exists_tiltedUnitSpline_conductor_uniform_reciprocalUpward_variable_rate


/-- Every logarithmic conductor family shares the actual upward-source bound,
including both prime-index cutoffs and the logarithmic kernel. -/
theorem exists_actualUpward_uniform_conductor_variable_rate {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ A : ℝ, 0 ≤ A → ∀ k : ℕ, 1 ≤ k → ∀ᶠ N : ℕ in atTop,
      ∀ m : ℕ, 0 < m → (m : ℝ) ≤ Real.log (N : ℝ) ^ A →
      ∀ c : ℝ, 1 ≤ c → 4 * (Real.exp 1 + 3) ^ 2 * c ^ 2 ≤ (N : ℝ) →
        (∑ n ∈ Icc 1 N, actualUpwardRowError φ c N m n ^ 2) / Real.log N ≤
          K * (m.totient : ℝ) ^ 2 *
            (c ^ 5 / Real.log N + c ^ 10 * (Real.log (N : ℝ) / N) ^ 2 +
              c ^ 3 * Real.log N ^ (1 / (k : ℝ)) / Real.log N) := by
  obtain ⟨Ca, hCa, ha⟩ := exists_logarithmicUpward_uniform_conductor_harmonic_bound hφ hsupp hM
  obtain ⟨Cs, hCs, hs⟩ := exists_conductor_uniform_reciprocalUpward_variable_rate hφ hsupp hM
  let d : ℝ := Real.exp 1 + 2
  let Ca' := Ca * d ^ 6
  let Cb' := (10 * (32 : ℝ) ^ 2) * d ^ 5
  have hd : 0 < d := by dsimp only [d]; positivity
  have hCa' : 0 ≤ Ca' := by dsimp only [Ca']; positivity
  have hCb' : 0 ≤ Cb' := by dsimp only [Cb']; positivity
  let K := 3 * (Ca' + Cb' + Cs)
  refine ⟨K, by dsimp only [K]; positivity, fun A hA k hk => ?_⟩
  have hloglim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hs A hA k hk, eventually_ge_atTop 1, hloglim.eventually_ge_atTop 1]
    with N hsource hN hlog
  intro m hm hmN c hc hlarge
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hL0 : 0 < Real.log N := zero_lt_one.trans_le hlog
  let B := linearPrimeStrip c
  have hBc : (B : ℝ) ≤ (Real.exp 1 + 1) * c := linearPrimeStrip_le hc
  have hB1 : (B : ℝ) + 1 ≤ d * c := by dsimp only [d]; nlinarith only [hBc, hc]
  have hc2 : c ≤ c ^ 2 := by nlinarith only [hc]
  have hexp := Real.exp_pos 1
  have hwidth : c / N ≤ 1 := by
    apply (div_le_one hN0).mpr
    have hcoef : 1 ≤ 4 * (Real.exp 1 + 3) ^ 2 := by nlinarith only [hexp]
    have h := mul_le_mul_of_nonneg_right hcoef (sq_nonneg c)
    nlinarith only [hlarge, hc2, h]
  have hcN : c ≤ (N : ℝ) := (div_le_one hN0).mp hwidth
  have hBN : B ≤ N := by
    have hcoef : Real.exp 1 + 1 ≤ 4 * (Real.exp 1 + 3) ^ 2 := by nlinarith only [hexp]
    have h1 := mul_le_mul_of_nonneg_left hc2 (show 0 ≤ Real.exp 1 + 1 by positivity)
    have h2 := mul_le_mul_of_nonneg_right hcoef (sq_nonneg c)
    have h : (B : ℝ) ≤ N := by nlinarith only [hBc, h1, h2, hlarge]
    exact_mod_cast h
  have hkernel : 2 * ((Real.exp 1 + 3) * c) * B ≤ (N : ℝ) := by
    have hcoef : 2 * (Real.exp 1 + 3) * (Real.exp 1 + 1) ≤
        4 * (Real.exp 1 + 3) ^ 2 := by nlinarith only [hexp]
    have h1 := mul_le_mul_of_nonneg_left hBc
      (show 0 ≤ 2 * ((Real.exp 1 + 3) * c) by positivity)
    have h2 := mul_le_mul_of_nonneg_right hcoef (sq_nonneg c)
    nlinarith only [h1, h2, hlarge]
  have hB : ⌈c⌉₊ ≤ B := by
    apply Nat.ceil_le.mpr
    have h := mul_le_mul_of_nonneg_left
      (Real.one_le_exp_iff.mpr (by norm_num : (0 : ℝ) ≤ 1)) hc0.le
    have hce : c ≤ c * Real.exp 1 := by simpa only [mul_one] using h
    exact hce.trans (Nat.le_ceil _)
  let R := c ^ 5 / Real.log N + c ^ 10 * (Real.log (N : ℝ) / N) ^ 2 +
    c ^ 3 * Real.log N ^ (1 / (k : ℝ)) / Real.log N
  have hR1 : c ^ 5 / Real.log N ≤ R := by
    dsimp only [R]
    exact (le_add_of_nonneg_right (by positivity : 0 ≤ c ^ 10 * (Real.log (N : ℝ) / N) ^ 2)).trans
      (le_add_of_nonneg_right (by positivity))
  have hR2 : c ^ 10 * (Real.log (N : ℝ) / N) ^ 2 ≤ R := by
    dsimp only [R]
    have h1 : 0 ≤ c ^ 5 / Real.log N := by positivity
    have h3 : 0 ≤ c ^ 3 * Real.log N ^ (1 / (k : ℝ)) / Real.log N := by positivity
    linarith only [h1, h3]
  have hR3 : c ^ 3 * Real.log N ^ (1 / (k : ℝ)) / Real.log N ≤ R := by
    dsimp only [R]
    exact le_add_of_nonneg_left (by positivity)
  let a : ℕ → ℝ := fun n =>
    (logarithmicUpwardCoefficient φ c B N m n - linearizedUpwardCoefficient φ c B N m n) / Real.sqrt n
  let b : ℕ → ℝ := fun n =>
    (linearizedUpwardCoefficient φ c B N m n - reciprocalUpwardCoefficient φ c B N m n) / Real.sqrt n
  let r : ℕ → ℝ := fun n =>
    (reciprocalUpwardCoefficient φ c B N m n -
      ramanujanLagCoefficient m n * shellCorrection φ c m) / Real.sqrt n
  have ha' : (∑ n ∈ Icc 1 N, a n ^ 2) / Real.log N ≤ Ca' * (m.totient : ℝ) ^ 2 * R := by
    have hp := pow_le_pow_left₀ (show 0 ≤ (B : ℝ) + 1 by positivity) hB1 6
    have hb := (ha m N hN hlog c hc hwidth B hBN hkernel).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hp (show 0 ≤ Ca * (m.totient : ℝ) ^ 2 * c ^ 4 by positivity))
        (sq_nonneg (Real.log (N : ℝ) / N)))
    have hb' : (∑ n ∈ Icc 1 N, a n ^ 2) / Real.log N ≤
        Ca' * (m.totient : ℝ) ^ 2 * (c ^ 10 * (Real.log (N : ℝ) / N) ^ 2) :=
      hb.trans_eq (by dsimp only [Ca']; ring)
    exact hb'.trans (mul_le_mul_of_nonneg_left hR2 (by positivity))
  have hb' : (∑ n ∈ Icc 1 N, b n ^ 2) / Real.log N ≤ Cb' * (m.totient : ℝ) ^ 2 * R := by
    have hb := linearizedUpwardCoefficient_boundary_uniform_conductor_budget hφ hsupp hM hm
      N hN c hc0 hcN B
    have hp := pow_le_pow_left₀ (show 0 ≤ (B : ℝ) + 1 by positivity) hB1 5
    have hb₀ := hb.trans (mul_le_mul_of_nonneg_left hp (by positivity))
    have hb₁ : (∑ n ∈ Icc 1 N, b n ^ 2) / Real.log N ≤
        Cb' * (m.totient : ℝ) ^ 2 * (c ^ 5 / Real.log N) := by
      exact (div_le_div_of_nonneg_right hb₀ hL0.le).trans_eq (by dsimp only [Cb']; ring)
    exact hb₁.trans (mul_le_mul_of_nonneg_left hR1 (by positivity))
  have hr' : (∑ n ∈ Icc 1 N, r n ^ 2) / Real.log N ≤ Cs * (m.totient : ℝ) ^ 2 * R := by
    have hb := hsource m hm hmN c hc B hB
    calc
      _ ≤ Cs * (m.totient : ℝ) ^ 2 * c ^ 3 * Real.log N ^ (1 / (k : ℝ)) / Real.log N := hb
      _ = (Cs * (m.totient : ℝ) ^ 2) *
          (c ^ 3 * Real.log N ^ (1 / (k : ℝ)) / Real.log N) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hR3 (by positivity)
  have hrow (n : ℕ) (hn : n ∈ Icc 1 N) : actualUpwardRowError φ c N m n = a n + b n + r n := by
    have hsqrt : Real.sqrt n ≠ 0 := (Real.sqrt_pos.mpr
      (by exact_mod_cast (mem_Icc.mp hn).1 : (0 : ℝ) < n)).ne'
    have hu : upwardPrimeRow (atomDilate φ (c / N)) N
        (fun j => ramanujanLagCoefficient m j / Real.sqrt j) n /
          (∫ u, atomDilate φ (c / N) u ^ 2) =
        logarithmicUpwardCoefficient φ c B N m n / Real.sqrt n := by
      apply (eq_div_iff hsqrt).mpr
      simpa only [mul_comm] using sqrt_mul_upwardRamanujanRow_eq_logarithmicCoefficient_small_width
        hsupp hc0 hn hwidth m
    rw [actualUpwardRowError, hu]
    dsimp only [a, b, r]
    ring
  have hsum : (∑ n ∈ Icc 1 N, actualUpwardRowError φ c N m n ^ 2) ≤
      ∑ n ∈ Icc 1 N, 3 * (a n ^ 2 + b n ^ 2 + r n ^ 2) := by
    apply sum_le_sum
    intro n hn
    rw [hrow n hn]
    nlinarith only [sq_nonneg (a n - b n), sq_nonneg (a n - r n), sq_nonneg (b n - r n)]
  have hfinal := div_le_div_of_nonneg_right hsum hL0.le
  rw [← mul_sum, sum_add_distrib, sum_add_distrib, mul_div_assoc, add_div, add_div] at hfinal
  exact hfinal.trans ((mul_le_mul_of_nonneg_left (add_le_add (add_le_add ha' hb') hr')
    (by norm_num : (0 : ℝ) ≤ 3)).trans_eq (by dsimp only [K, R]; ring))

/-- The norm of the literal upward residual is uniform over logarithmic conductor families. -/
theorem exists_normalizedUpward_uniform_conductor_variable_rate {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ A : ℝ, 0 ≤ A → ∀ k : ℕ, 1 ≤ k → ∀ᶠ N : ℕ in atTop,
      ∀ m : ℕ, 0 < m → (m : ℝ) ≤ Real.log (N : ℝ) ^ A →
      ∀ c : ℝ, 1 ≤ c → 4 * (Real.exp 1 + 3) ^ 2 * c ^ 2 ≤ (N : ℝ) →
        ‖normalizedUpwardPrimeResidual φ c N m‖ ^ 2 ≤ K * (m.totient : ℝ) ^ 2 *
          (c ^ 5 / Real.log N + c ^ 10 * (Real.log (N : ℝ) / N) ^ 2 +
            c ^ 3 * Real.log N ^ (1 / (k : ℝ)) / Real.log N) := by
  simpa only [normalizedUpwardPrimeResidual_norm_sq] using
    exists_actualUpward_uniform_conductor_variable_rate hφ hsupp hM

#print axioms exists_actualUpward_uniform_conductor_variable_rate
#print axioms exists_normalizedUpward_uniform_conductor_variable_rate


private theorem norm_add_sq_le_two_variable {E : Type*} [SeminormedAddCommGroup E] (a b : E) :
    ‖a + b‖ ^ 2 ≤ 2 * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le a b) 2
  nlinarith only [h, sq_nonneg (‖a‖ - ‖b‖)]

private theorem norm_four_sq_le_variable {E : Type*} [SeminormedAddCommGroup E] (a b c d : E) :
    ‖a + b + c + d‖ ^ 2 ≤ 4 * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2 + ‖d‖ ^ 2) := by
  have h := norm_add_sq_le_two_variable (a + b) (c + d)
  rw [← add_assoc] at h
  linarith only [h, norm_add_sq_le_two_variable a b, norm_add_sq_le_two_variable c d]

private theorem norm_eight_signed_sq_le_variable {E : Type*} [SeminormedAddCommGroup E]
    (p s c x q y z u : E) :
    ‖-p + s + c - x + q + (y + z) - u‖ ^ 2 ≤
      8 * (‖p‖ ^ 2 + ‖s‖ ^ 2 + ‖c‖ ^ 2 + ‖x‖ ^ 2 +
        ‖q‖ ^ 2 + ‖y‖ ^ 2 + ‖z‖ ^ 2 + ‖u‖ ^ 2) := by
  have hid : -p + s + c - x + q + (y + z) - u =
      (-p + s + c + -x) + (q + y + z + -u) := by abel
  rw [hid]
  have h := norm_add_sq_le_two_variable (-p + s + c + -x) (q + y + z + -u)
  have h1 := norm_four_sq_le_variable (-p) s c (-x)
  have h2 := norm_four_sq_le_variable q y z (-u)
  rw [norm_neg, norm_neg] at h1
  rw [norm_neg] at h2
  linarith only [h, h1, h2]

private theorem conductor_power_variable_rate_le {t : ℕ} {C c L N m : ℝ}
    (hC : 0 ≤ C) (hc : 1 ≤ c) (hm : 1 ≤ m) (hL : 0 ≤ L)
    {j k : ℕ} (hj : j ≤ 4) (hk : k ≤ 5) :
    C * m ^ j * c ^ k / L ≤ C * m ^ 4 *
      (c ^ 5 / L + c ^ 10 * (L / N) ^ 2 + c ^ 3 * L ^ (1 / (t : ℝ)) / L) := by
  have hm0 := zero_le_one.trans hm
  have hc0 := zero_le_one.trans hc
  calc
    _ ≤ C * m ^ 4 * c ^ 5 / L := by
      apply div_le_div_of_nonneg_right _ hL
      exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hm hj) hC)
        (pow_le_pow_right₀ hc hk) (by positivity) (by positivity)
    _ = C * m ^ 4 * (c ^ 5 / L) := by ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (le_add_of_nonneg_right (by positivity : 0 ≤ c ^ 10 * (L / N) ^ 2)).trans
        (le_add_of_nonneg_right (by positivity))

private theorem inv_sqrt_totient_sq_le_one_variable {m : ℕ} (hm : 0 < m) :
    (Real.sqrt (m.totient : ℝ))⁻¹ ^ 2 ≤ 1 := by
  have ht : (1 : ℝ) ≤ m.totient := by exact_mod_cast Nat.totient_pos.mpr hm
  rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg m.totient)]
  simpa only [one_div] using (div_le_one (zero_lt_one.trans_le ht)).mpr ht

/-- Every term of the complete signed residual shares a quartic conductor budget.
The waiting horizon is common to all conductors in any fixed logarithmic range. -/
theorem exists_completeWeil_uniform_conductor_residual_variable_rate {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ A : ℝ, 0 ≤ A → ∀ k : ℕ, 1 ≤ k → ∀ᶠ N : ℕ in atTop,
      ∀ m : ℕ, 0 < m → (m : ℝ) ≤ Real.log (N : ℝ) ^ A →
      ∀ c : ℝ, 1 ≤ c → 4 * (Real.exp 1 + 3) ^ 2 * c ^ 2 ≤ (N : ℝ) →
        ‖Matrix.toEuclideanLin (completeWeilMatrix φ c N) (normalizedRamanujanHorizonVector m N) -
          completedConductorEnergy φ c m • normalizedRamanujanHorizonVector m N‖ ^ 2 ≤
          K * (m : ℝ) ^ 4 * (c ^ 5 / Real.log N +
            c ^ 10 * (Real.log (N : ℝ) / N) ^ 2 + c ^ 3 * Real.log N ^ (1 / (k : ℝ)) / Real.log N) := by
  obtain ⟨Cp, hCp, hp⟩ := exists_primeResidual_uniform_conductor_bound
  obtain ⟨Cs, hCs, hs⟩ := exists_selfError_uniform_conductor_bound hφ hsupp hM
  obtain ⟨Cc, hCc, hcenter⟩ := exists_centerError_uniform_conductor_bound φ
  obtain ⟨Cx, hCx, hx⟩ := exists_crossError_uniform_conductor_bound hφ hsupp hM
  obtain ⟨Cq, hCq, hq⟩ := exists_poleError_uniform_conductor_bound hφ hsupp hM
  obtain ⟨Cd, hCd, hdown⟩ := exists_fullNearGammaDownward_uniform_conductor_bound hφ hsupp hM
  obtain ⟨Cn, hCn, hnear⟩ := exists_nearCenter_uniform_conductor_bound hM
  obtain ⟨Cu, hCu, hup⟩ := exists_normalizedUpward_uniform_conductor_variable_rate hφ hsupp hM
  let K := 8 * (Cp + Cs + Cc + Cx + Cq + Cd + Cn + Cu) + 1
  refine ⟨K, by dsimp only [K]; positivity, ?_⟩
  intro A hA k hk
  have hloglim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hup A hA k hk, eventually_ge_atTop 1, hloglim.eventually_ge_atTop 1]
    with N hupN hN hlog
  intro m hm hmN c hc hlarge
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 := zero_le_one.trans hm1
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hL0 : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hlog
  let R := c ^ 5 / Real.log N + c ^ 10 * (Real.log (N : ℝ) / N) ^ 2 +
    c ^ 3 * Real.log N ^ (1 / (k : ℝ)) / Real.log N
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  have hthree : 3 * c ≤ (N : ℝ) := by
    have he := Real.exp_pos 1
    have hcoef : 3 ≤ 4 * (Real.exp 1 + 3) ^ 2 := by nlinarith only [he]
    have hc2 : c ≤ c ^ 2 := by nlinarith only [hc]
    have h := mul_le_mul_of_nonneg_right hcoef (sq_nonneg c)
    nlinarith only [h, hc2, hlarge]
  have hcN : c ≤ (N : ℝ) := by linarith only [hthree, hc0]
  have htwo : 2 * c ≤ (N : ℝ) := by linarith only [hthree, hc0]
  have hw : c / N ≤ 1 / 3 := by
    rw [div_le_iff₀ hN0]
    linarith only [hthree]
  have hp' : ‖Matrix.toEuclideanLin (fullPrimeMatrix N) (normalizedRamanujanHorizonVector m N) -
      (Real.log N - ramanujanAdjunctionEnergy m) • normalizedRamanujanHorizonVector m N‖ ^ 2 ≤
      Cp * (m : ℝ) ^ 4 * R := by
    have hb := conductor_power_variable_rate_le (t := k) (N := (N : ℝ)) hCp.le hc hm1 hL0.le
      (j := 3) (k := 0) (by norm_num) (by norm_num)
    simp only [pow_zero, mul_one] at hb
    exact (hp m hm N).trans hb
  have hs' : ‖completeWeilSelfError φ c N • normalizedRamanujanHorizonVector m N‖ ^ 2 ≤
      Cs * (m : ℝ) ^ 4 * R := by
    have hm24 := pow_le_pow_right₀ hm1 (by norm_num : 2 ≤ 4)
    have hc210 := pow_le_pow_right₀ hc (by norm_num : 2 ≤ 10)
    have hL2 : 1 ≤ Real.log (N : ℝ) ^ 2 := one_le_pow₀ hlog
    have hscale := mul_le_mul_of_nonneg_left hL2 (pow_nonneg hc0.le 10)
    have hnum : Cs * (m : ℝ) ^ 2 * c ^ 2 ≤
        Cs * (m : ℝ) ^ 4 * (c ^ 10 * Real.log (N : ℝ) ^ 2) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hm24 hCs.le)
        (hc210.trans (by simpa only [mul_one] using hscale)) (sq_nonneg _) (by positivity)
    calc
      _ ≤ Cs * (m : ℝ) ^ 2 * c ^ 2 / (N : ℝ) ^ 2 := hs m hm N hN hlog c hc0 hcN
      _ ≤ (Cs * (m : ℝ) ^ 4 * (c ^ 10 * Real.log (N : ℝ) ^ 2)) / (N : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right hnum (sq_nonneg _)
      _ = Cs * (m : ℝ) ^ 4 * (c ^ 10 * (Real.log (N : ℝ) / N) ^ 2) := by
        rw [div_pow]; ring
      _ ≤ Cs * (m : ℝ) ^ 4 * R := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        dsimp only [R]
        have h1 : 0 ≤ c ^ 5 / Real.log N := by positivity
        have h3 : 0 ≤ c ^ 3 * Real.log N ^ (1 / (k : ℝ)) / Real.log N := by positivity
        linarith only [h1, h3]
  have hc' := (hcenter m hm c N).trans
    (conductor_power_variable_rate_le (t := k) (N := (N : ℝ)) hCc hc hm1 hL0.le
      (by norm_num : 2 ≤ 4) (by norm_num : 2 ≤ 5))
  have hx' := (hx m hm c hc0 N hN).trans
    (conductor_power_variable_rate_le (t := k) (N := (N : ℝ)) hCx hc hm1 hL0.le
      (by norm_num : 2 ≤ 4) (by norm_num : 4 ≤ 5))
  have hq' := (hq m hm c hc0 N hN hcN).trans
    (conductor_power_variable_rate_le (t := k) (N := (N : ℝ)) hCq hc hm1 hL0.le
      (by norm_num : 2 ≤ 4) (by norm_num : 4 ≤ 5))
  have hn' := (hnear m hm c hc N hN htwo).trans
    (conductor_power_variable_rate_le (t := k) (N := (N : ℝ)) hCn hc hm1 hL0.le
      (by norm_num : 2 ≤ 4) (by norm_num : 5 ≤ 5))
  have hd' : ‖(Real.sqrt (m.totient : ℝ))⁻¹ • normalizedFullNearGammaDownwardVector φ c N m‖ ^ 2 ≤
      Cd * (m : ℝ) ^ 4 * R := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    have hb := (hdown m hm c hc N hN hw).trans
      (conductor_power_variable_rate_le (t := k) (N := (N : ℝ)) hCd hc hm1 hL0.le
        (by norm_num : 4 ≤ 4) (by norm_num : 5 ≤ 5))
    exact (mul_le_mul (inv_sqrt_totient_sq_le_one_variable hm) hb (sq_nonneg _) zero_le_one).trans_eq
      (by rw [one_mul])
  have hu' : ‖upwardPrimeVector φ c N (normalizedRamanujanHorizonVector m N) -
      shellCorrection φ c m • normalizedRamanujanHorizonVector m N‖ ^ 2 ≤
      Cu * (m : ℝ) ^ 4 * R := by
    rw [upwardPrimeVector_ramanujan_residual_eq φ c N hm, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    have ht : (m.totient : ℝ) ≤ m := by exact_mod_cast Nat.totient_le m
    have ht4 : (m.totient : ℝ) ^ 2 ≤ (m : ℝ) ^ 4 :=
      (pow_le_pow_left₀ (Nat.cast_nonneg m.totient) ht 2).trans
        (pow_le_pow_right₀ hm1 (by norm_num))
    have hb := (hupN m hm hmN c hc hlarge).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht4 hCu.le) hR)
    exact (mul_le_mul (inv_sqrt_totient_sq_le_one_variable hm) hb (sq_nonneg _) zero_le_one).trans_eq
      (by rw [one_mul])
  rw [completeWeilMatrix_ramanujan_residual_eq_at_every_overlap hφ hsupp hM hc0 hN hm]
  have hsum := norm_eight_signed_sq_le_variable
    (Matrix.toEuclideanLin (fullPrimeMatrix N) (normalizedRamanujanHorizonVector m N) -
      (Real.log N - ramanujanAdjunctionEnergy m) • normalizedRamanujanHorizonVector m N)
    (completeWeilSelfError φ c N • normalizedRamanujanHorizonVector m N)
    (Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift φ c) N)
      (normalizedRamanujanHorizonVector m N) -
      (if m = 1 then completeWeilPoleShift φ c else 0) • normalizedRamanujanHorizonVector m N)
    (Matrix.toEuclideanLin (separatedCrossErrorMatrix φ c N) (normalizedRamanujanHorizonVector m N))
    (Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ c N) (normalizedRamanujanHorizonVector m N))
    ((Real.sqrt (m.totient : ℝ))⁻¹ • normalizedFullNearGammaDownwardVector φ c N m)
    (nearCenterVector φ c N m)
    (upwardPrimeVector φ c N (normalizedRamanujanHorizonVector m N) -
      shellCorrection φ c m • normalizedRamanujanHorizonVector m N)
  have hb := hsum.trans (mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add hp' hs') hc') hx') hq') hd') hn') hu')
    (by norm_num : (0 : ℝ) ≤ 8))
  change _ ≤ K * (m : ℝ) ^ 4 * R
  calc
    _ ≤ 8 * (Cp * (m : ℝ) ^ 4 * R + Cs * (m : ℝ) ^ 4 * R +
        Cc * (m : ℝ) ^ 4 * R + Cx * (m : ℝ) ^ 4 * R + Cq * (m : ℝ) ^ 4 * R +
        Cd * (m : ℝ) ^ 4 * R + Cn * (m : ℝ) ^ 4 * R + Cu * (m : ℝ) ^ 4 * R) := hb
    _ = (8 * (Cp + Cs + Cc + Cx + Cq + Cd + Cn + Cu)) * (m : ℝ) ^ 4 * R := by ring
    _ ≤ K * (m : ℝ) ^ 4 * R := by
      apply mul_le_mul_of_nonneg_right _ hR
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hm0 4)
      dsimp only [K]
      linarith only

/-- The explicit tilted spline has a common complete-residual bound on logarithmic conductor ranges. -/
theorem exists_tiltedUnitSpline_uniform_conductor_residual_variable_rate :
    ∃ K : ℝ, 0 < K ∧ ∀ A : ℝ, 0 ≤ A → ∀ k : ℕ, 1 ≤ k → ∀ᶠ N : ℕ in atTop,
      ∀ m : ℕ, 0 < m → (m : ℝ) ≤ Real.log (N : ℝ) ^ A →
      ∀ c : ℝ, 1 ≤ c → 4 * (Real.exp 1 + 3) ^ 2 * c ^ 2 ≤ (N : ℝ) →
        ‖Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
          (normalizedRamanujanHorizonVector m N) -
          completedConductorEnergy tiltedUnitSpline c m • normalizedRamanujanHorizonVector m N‖ ^ 2 ≤
          K * (m : ℝ) ^ 4 * (c ^ 5 / Real.log N +
            c ^ 10 * (Real.log (N : ℝ) / N) ^ 2 + c ^ 3 * Real.log N ^ (1 / (k : ℝ)) / Real.log N) :=
  exists_completeWeil_uniform_conductor_residual_variable_rate contDiff_tiltedUnitSpline
    tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos


end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_completeWeil_uniform_conductor_residual_variable_rate
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_tiltedUnitSpline_uniform_conductor_residual_variable_rate
