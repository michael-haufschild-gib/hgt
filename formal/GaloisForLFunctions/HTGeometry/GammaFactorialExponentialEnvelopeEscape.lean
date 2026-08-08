import GaloisForLFunctions.HTGeometry.GammaFactorialThirdJetHarmonicResidue
import GaloisForLFunctions.HTGeometry.PolygammaReflection

/-!
# Escape from the exponential-reciprocal envelope

The dominant harmonic expansion of the factorial Gamma pole germ is not free: it lies in the
two-parameter family `-C exp(a x)/x`.  That entire envelope satisfies the third-order differential
discriminant

`(y²y''' - 3yy'y'' + 2(y')³)² - 4(yy'' - (y')²)³ = 0`.

Consequently harmonic degree alone cannot make the pole-germ residue map injective.  This file
resolves the first layer below that envelope.  At the pure factorial scale `sₙ²`, the exact Gamma
germ crosses the discriminant with coefficient `-24 ζ(2)`, or `-4π²`.  Thus the pole microscope is
intrinsically bifiltered: unbounded harmonic deformation sits above a bounded zeta layer.

All limits are proved from exact shift formulae and convergent series; no numerical approximation
is used.
-/

namespace GaloisForLFunctions

open Complex Filter Topology

noncomputable section

open scoped BigOperators

theorem norm_shiftedInverse_sub_inverse_le {z : ℂ}
    (hz : ‖z‖ ≤ 1 / 2) (j : ℕ) :
    ‖(((j + 1 : ℕ) : ℂ) - z)⁻¹ - (((j + 1 : ℕ) : ℂ))⁻¹‖ ≤
      2 * ‖z‖ / ((j + 1 : ℕ) : ℝ) ^ 2 := by
  let k : ℝ := ((j + 1 : ℕ) : ℝ)
  let c : ℂ := ((j + 1 : ℕ) : ℂ)
  have hk : 1 ≤ k := by
    dsimp [k]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le j)
  have hkpos : 0 < k := lt_of_lt_of_le zero_lt_one hk
  have hcNorm : ‖c‖ = k := by
    dsimp [c, k]
    rw [Complex.norm_natCast]
  have hc : c ≠ 0 := by
    intro h
    have := congrArg norm h
    rw [hcNorm, norm_zero] at this
    linarith
  have hcz : c - z ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    have hn := congrArg norm h
    rw [hcNorm] at hn
    nlinarith
  have hshift := norm_shiftedInverse_le hz j
  have hcInv : ‖c⁻¹‖ = k⁻¹ := by
    rw [norm_inv, hcNorm]
  change ‖(c - z)⁻¹ - c⁻¹‖ ≤ _
  rw [inv_sub_inv' hcz hc]
  rw [show c - (c - z) = z by ring]
  rw [norm_mul, norm_mul, hcInv]
  calc
    ‖(c - z)⁻¹‖ * ‖z‖ * k⁻¹ ≤ (2 / k) * ‖z‖ * k⁻¹ := by
      gcongr
    _ = 2 * ‖z‖ / k ^ 2 := by field_simp

theorem norm_shiftedInverseSquare_sub_inverseSquare_le {z : ℂ}
    (hz : ‖z‖ ≤ 1 / 2) (j : ℕ) :
    ‖((((j + 1 : ℕ) : ℂ) - z) ^ 2)⁻¹ -
        ((((j + 1 : ℕ) : ℂ) ^ 2)⁻¹)‖ ≤
      6 * ‖z‖ / ((j + 1 : ℕ) : ℝ) := by
  let k : ℝ := ((j + 1 : ℕ) : ℝ)
  let c : ℂ := ((j + 1 : ℕ) : ℂ)
  let u : ℂ := (c - z)⁻¹
  let v : ℂ := c⁻¹
  have hk : 1 ≤ k := by
    dsimp [k]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le j)
  have hkpos : 0 < k := lt_of_lt_of_le zero_lt_one hk
  have hu : ‖u‖ ≤ 2 / k := by
    simpa [u, c, k] using norm_shiftedInverse_le hz j
  have hv : ‖v‖ = 1 / k := by
    dsimp [v, c, k]
    rw [norm_inv, Complex.norm_natCast]
    ring
  have hdiff : ‖u - v‖ ≤ 2 * ‖z‖ / k ^ 2 := by
    simpa [u, v, c, k] using norm_shiftedInverse_sub_inverse_le hz j
  have hadd : ‖u + v‖ ≤ 3 / k := by
    calc
      ‖u + v‖ ≤ ‖u‖ + ‖v‖ := norm_add_le _ _
      _ ≤ 2 / k + 1 / k := add_le_add hu hv.le
      _ = 3 / k := by ring
  have hprod : ‖(u - v) * (u + v)‖ ≤
      (2 * ‖z‖ / k ^ 2) * (3 / k) := by
    rw [norm_mul]
    gcongr
  change ‖((c - z) ^ 2)⁻¹ - (c ^ 2)⁻¹‖ ≤ 6 * ‖z‖ / k
  rw [← inv_pow, ← inv_pow]
  rw [show u ^ 2 - v ^ 2 = (u - v) * (u + v) by ring]
  calc
    ‖(u - v) * (u + v)‖ ≤ (2 * ‖z‖ / k ^ 2) * (3 / k) := hprod
    _ ≤ 6 * ‖z‖ / k := by
      have hk2 : 1 ≤ k ^ 2 := by nlinarith
      have hmul := mul_le_mul_of_nonneg_left hk2
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 6) (norm_nonneg z))
      field_simp [hkpos.ne']
      nlinarith [hmul]

theorem norm_shiftedHarmonicSquareSum_sub_unshifted_le {z : ℂ}
    (hz : ‖z‖ ≤ 1 / 2) (n : ℕ) :
    ‖shiftedHarmonicSquareSum n z -
        ∑ j ∈ Finset.range n, ((((j + 1 : ℕ) : ℂ) ^ 2)⁻¹)‖ ≤
      6 * ‖z‖ * (harmonic n : ℝ) := by
  rw [shiftedHarmonicSquareSum, ← Finset.sum_sub_distrib]
  calc
    ‖∑ j ∈ Finset.range n,
        (((((j + 1 : ℕ) : ℂ) - z) ^ 2)⁻¹ -
          ((((j + 1 : ℕ) : ℂ) ^ 2)⁻¹))‖ ≤
        ∑ j ∈ Finset.range n,
          ‖((((j + 1 : ℕ) : ℂ) - z) ^ 2)⁻¹ -
            ((((j + 1 : ℕ) : ℂ) ^ 2)⁻¹)‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range n,
        6 * ‖z‖ / ((j + 1 : ℕ) : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      exact norm_shiftedInverseSquare_sub_inverseSquare_le hz j
    _ = 6 * ‖z‖ * (harmonic n : ℝ) := by
      rw [harmonic]
      push_cast
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      field_simp

theorem tendsto_unshiftedHarmonicSquareSum_pi_sq_div_six :
    Tendsto (fun n : ℕ =>
      ∑ j ∈ Finset.range n, ((((j + 1 : ℕ) : ℂ) ^ 2)⁻¹)) atTop
      (𝓝 ((Real.pi : ℂ) ^ 2 / 6)) := by
  have hzeta : HasSum (fun n : ℕ => (1 : ℂ) / (n : ℂ) ^ 2)
      ((Real.pi : ℂ) ^ 2 / 6) := by
    have hreal : HasSum (fun n : ℕ => ((1 / (n : ℝ) ^ 2 : ℝ) : ℂ))
        (((Real.pi ^ 2 / 6 : ℝ) : ℂ)) :=
      Complex.hasSum_ofReal.mpr hasSum_zeta_two
    simpa using hreal
  have h := hzeta.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  convert h using 1
  funext n
  change (∑ j ∈ Finset.range n, ((((j + 1 : ℕ) : ℂ) ^ 2)⁻¹)) =
    ∑ i ∈ Finset.range (n + 1), (1 : ℂ) / (i : ℂ) ^ 2
  rw [Finset.sum_range_succ']
  norm_num

theorem tendsto_shiftedHarmonicSquareSum_factorial
    (x : ℂ) :
    Tendsto (fun n : ℕ => shiftedHarmonicSquareSum n
      (reciprocalGammaFactorialScale n * x)) atTop
      (𝓝 ((Real.pi : ℂ) ^ 2 / 6)) := by
  let z : ℕ → ℂ := fun n => reciprocalGammaFactorialScale n * x
  have hz : Tendsto z atTop (𝓝 0) := by
    simpa [z] using tendsto_reciprocalGammaFactorialScale_zero.mul_const x
  have hsmall : ∀ᶠ n : ℕ in atTop, ‖z n‖ ≤ 1 / 2 :=
    (hz.norm.eventually_lt_const (by norm_num)).mono fun _ h => h.le
  have hmajor : Tendsto (fun n => 6 * ‖z n‖ * (harmonic n : ℝ))
      atTop (𝓝 0) := by
    have h := tendsto_gammaHarmonicMicroscopeScale_zero.norm.const_mul
      (6 * ‖x‖)
    convert h using 1
    · funext n
      have hnormH : ‖(harmonic n : ℂ)‖ = (harmonic n : ℝ) := by
        rw [show (harmonic n : ℂ) = ((harmonic n : ℝ) : ℂ) by norm_cast]
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
        exact_mod_cast (show (0 : ℚ) ≤ harmonic n by
          rw [harmonic]
          positivity)
      simp only [z, gammaHarmonicMicroscopeScale, norm_mul, hnormH]
      ring
    · norm_num
  have hdiff : Tendsto (fun n =>
      shiftedHarmonicSquareSum n (z n) -
        ∑ j ∈ Finset.range n, ((((j + 1 : ℕ) : ℂ) ^ 2)⁻¹))
      atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero' (Filter.Eventually.of_forall fun n => norm_nonneg _) _ hmajor
    filter_upwards [hsmall] with n hn
    exact norm_shiftedHarmonicSquareSum_sub_unshifted_le hn n
  have hsum := hdiff.add tendsto_unshiftedHarmonicSquareSum_pi_sq_div_six
  have heq : ∀ n : ℕ,
      (shiftedHarmonicSquareSum n (z n) -
          (∑ j ∈ Finset.range n, ((((j + 1 : ℕ) : ℂ) ^ 2)⁻¹)) +
        (∑ j ∈ Finset.range n, ((((j + 1 : ℕ) : ℂ) ^ 2)⁻¹))) =
      shiftedHarmonicSquareSum n (z n) := by
    intro n
    ring
  simpa [z] using hsum.congr' (Filter.Eventually.of_forall heq)

/-- The first correction below the dominant harmonic scale is the doubled trigamma value
`2 ψ'(1)=π²/3`. -/
theorem tendsto_gammaFactorialScaledTrigamma_div_factorialScale_sq
    {x : ℂ} (hx : x ≠ 0) :
    Tendsto (fun n : ℕ =>
      (gammaFactorialScaledTrigamma n x - x⁻¹ ^ 2) /
        reciprocalGammaFactorialScale n ^ 2) atTop
      (𝓝 ((Real.pi : ℂ) ^ 2 / 3)) := by
  let s : ℕ → ℂ := reciprocalGammaFactorialScale
  let z : ℕ → ℂ := fun n => s n * x
  have hz : Tendsto z atTop (𝓝 0) := by
    simpa [z, s] using tendsto_reciprocalGammaFactorialScale_zero.mul_const x
  have hinput : Tendsto (fun n => 1 + z n) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds.add hz :
      Tendsto (fun n => 1 + z n) atTop (𝓝 (1 + 0)))
  have hOff1 : ∀ k : ℕ, (1 : ℂ) ≠ -(k : ℂ) := by
    intro k hk
    have hre := congrArg Complex.re hk
    simp only [Complex.one_re, Complex.neg_re, Complex.natCast_re] at hre
    linarith [Nat.cast_nonneg (α := ℝ) k]
  have hpsi0 : Tendsto (fun n => iteratedDeriv 1 Complex.digamma (1 + z n))
      atTop (𝓝 (iteratedDeriv 1 Complex.digamma 1)) :=
    (analyticAt_iteratedDeriv_of_analyticAt
      (analyticAt_digamma_of_offPoles hOff1) 1).continuousAt.tendsto.comp hinput
  have hpsi : Tendsto (fun n => iteratedDeriv 1 Complex.digamma (1 + z n))
      atTop (𝓝 ((Real.pi : ℂ) ^ 2 / 6)) := by
    simpa only [iteratedDeriv_one, RHTower.trigamma_one] using hpsi0
  have hsum : Tendsto (fun n => shiftedHarmonicSquareSum n (z n))
      atTop (𝓝 ((Real.pi : ℂ) ^ 2 / 6)) := by
    simpa [z, s] using tendsto_shiftedHarmonicSquareSum_factorial x
  have hlimit := hpsi.add hsum
  have hlimit' : Tendsto (fun n =>
      iteratedDeriv 1 Complex.digamma (1 + z n) +
        shiftedHarmonicSquareSum n (z n)) atTop
      (𝓝 ((Real.pi : ℂ) ^ 2 / 3)) := by
    have hvalue : (Real.pi : ℂ) ^ 2 / 6 + (Real.pi : ℂ) ^ 2 / 6 =
        (Real.pi : ℂ) ^ 2 / 3 := by ring
    rw [hvalue] at hlimit
    exact hlimit
  have hregular : ∀ᶠ n : ℕ in atTop, ∀ k : ℤ, z n ≠ (k : ℂ) := by
    have hlt : ∀ᶠ n : ℕ in atTop, ‖z n‖ < 1 :=
      hz.norm.eventually_lt_const (by norm_num)
    filter_upwards [hlt] with n hzn k
    have hsn : s n ≠ 0 := by
      dsimp [s]
      exact div_ne_zero (pow_ne_zero _ (by norm_num))
        (by exact_mod_cast Nat.factorial_ne_zero n)
    exact ne_intCast_of_ne_zero_of_norm_lt_one (mul_ne_zero hsn hx) hzn k
  have heq : ∀ᶠ n : ℕ in atTop,
      (gammaFactorialScaledTrigamma n x - x⁻¹ ^ 2) / s n ^ 2 =
        iteratedDeriv 1 Complex.digamma (1 + z n) +
          shiftedHarmonicSquareSum n (z n) := by
    filter_upwards [hregular] with n hzn
    have hsn : s n ≠ 0 := by
      dsimp [s]
      exact div_ne_zero (pow_ne_zero _ (by norm_num))
        (by exact_mod_cast Nat.factorial_ne_zero n)
    have hformula := iteratedDeriv_one_digamma_neg_nat_add_of_ne_int (z n) hzn n
    rw [gammaFactorialScaledTrigamma]
    change (s n ^ 2 * iteratedDeriv 1 Complex.digamma (-↑n + z n) - x⁻¹ ^ 2) /
      s n ^ 2 = _
    rw [hformula]
    dsimp [z]
    field_simp [hsn, hx]
    ring
  exact hlimit'.congr' (heq.mono fun _ h => h.symm)

theorem tendsto_gammaFactorialScaledSecondPolygamma_div_factorialScale_sq
    {x : ℂ} (hx : x ≠ 0) :
    Tendsto (fun n : ℕ =>
      (gammaFactorialScaledSecondPolygamma n x - 2 * (-x)⁻¹ ^ 3) /
        reciprocalGammaFactorialScale n ^ 2) atTop (𝓝 0) := by
  let s : ℕ → ℂ := reciprocalGammaFactorialScale
  let z : ℕ → ℂ := fun n => s n * x
  have hs : Tendsto s atTop (𝓝 0) :=
    tendsto_reciprocalGammaFactorialScale_zero
  have hz : Tendsto z atTop (𝓝 0) := by
    simpa [z] using hs.mul_const x
  have hinput : Tendsto (fun n => 1 + z n) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds.add hz :
      Tendsto (fun n => 1 + z n) atTop (𝓝 (1 + 0)))
  have hOff1 : ∀ k : ℕ, (1 : ℂ) ≠ -(k : ℂ) := by
    intro k hk
    have hre := congrArg Complex.re hk
    simp only [Complex.one_re, Complex.neg_re, Complex.natCast_re] at hre
    linarith [Nat.cast_nonneg (α := ℝ) k]
  have hpsi : Tendsto (fun n => iteratedDeriv 2 Complex.digamma (1 + z n))
      atTop (𝓝 (iteratedDeriv 2 Complex.digamma 1)) :=
    (analyticAt_iteratedDeriv_of_analyticAt
      (analyticAt_digamma_of_offPoles hOff1) 2).continuousAt.tendsto.comp hinput
  have hlocal : Tendsto (fun n => s n *
      iteratedDeriv 2 Complex.digamma (1 + z n)) atTop (𝓝 0) := by
    simpa using hs.mul hpsi
  have hsmall : ∀ᶠ n : ℕ in atTop, ‖z n‖ ≤ 1 / 2 :=
    (hz.norm.eventually_lt_const (by norm_num)).mono fun _ h => h.le
  have hsum : Tendsto (fun n => 2 * s n * shiftedHarmonicCubeSum n (z n))
      atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hmajor : Tendsto (fun n => 16 * ‖gammaHarmonicMicroscopeScale n‖)
        atTop (𝓝 0) := by
      simpa using tendsto_gammaHarmonicMicroscopeScale_zero.norm.const_mul 16
    apply squeeze_zero' (Filter.Eventually.of_forall fun n => norm_nonneg _) _ hmajor
    filter_upwards [hsmall] with n hzn
    have hbound := norm_shiftedHarmonicCubeSum_le hzn n
    have hnormH : ‖(harmonic n : ℂ)‖ = (harmonic n : ℝ) := by
      rw [show (harmonic n : ℂ) = ((harmonic n : ℝ) : ℂ) by norm_cast]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
      exact_mod_cast (show (0 : ℚ) ≤ harmonic n by
        rw [harmonic]
        positivity)
    rw [norm_mul, norm_mul]
    have hnorm2 : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [hnorm2]
    change 2 * ‖s n‖ * ‖shiftedHarmonicCubeSum n (z n)‖ ≤ _
    rw [gammaHarmonicMicroscopeScale, norm_mul, hnormH]
    nlinarith [norm_nonneg (s n)]
  have hlimit : Tendsto (fun n => s n *
      (iteratedDeriv 2 Complex.digamma (1 + z n) +
        2 * shiftedHarmonicCubeSum n (z n))) atTop (𝓝 0) := by
    have h := hlocal.add hsum
    convert h using 1 <;> ring
  have hregular : ∀ᶠ n : ℕ in atTop, ∀ k : ℤ, z n ≠ (k : ℂ) := by
    have hlt : ∀ᶠ n : ℕ in atTop, ‖z n‖ < 1 :=
      hz.norm.eventually_lt_const (by norm_num)
    filter_upwards [hlt] with n hzn k
    have hsn : s n ≠ 0 := by
      dsimp [s]
      exact div_ne_zero (pow_ne_zero _ (by norm_num))
        (by exact_mod_cast Nat.factorial_ne_zero n)
    exact ne_intCast_of_ne_zero_of_norm_lt_one (mul_ne_zero hsn hx) hzn k
  have heq : ∀ᶠ n : ℕ in atTop,
      (gammaFactorialScaledSecondPolygamma n x - 2 * (-x)⁻¹ ^ 3) /
          s n ^ 2 =
        s n * (iteratedDeriv 2 Complex.digamma (1 + z n) +
          2 * shiftedHarmonicCubeSum n (z n)) := by
    filter_upwards [hregular] with n hzn
    have hsn : s n ≠ 0 := by
      dsimp [s]
      exact div_ne_zero (pow_ne_zero _ (by norm_num))
        (by exact_mod_cast Nat.factorial_ne_zero n)
    have hformula := iteratedDeriv_two_digamma_neg_nat_add_of_ne_int (z n) hzn n
    rw [gammaFactorialScaledSecondPolygamma]
    change (s n ^ 3 * iteratedDeriv 2 Complex.digamma (-↑n + z n) -
        2 * (-x)⁻¹ ^ 3) / s n ^ 2 = _
    rw [hformula]
    dsimp [z]
    field_simp [hsn, hx]
    ring
  exact hlimit.congr' (heq.mono fun _ h => h.symm)

/-- The differential discriminant of the logarithmic derivative.  It vanishes for every member of
the exponential-reciprocal envelope `-C exp(a x)/x`, not merely at its reciprocal limit. -/
def gammaFactorialLogCurvatureDiscriminant (n : ℕ) (x : ℂ) : ℂ :=
  gammaFactorialScaledSecondPolygamma n x ^ 2 -
    4 * gammaFactorialScaledTrigamma n x ^ 3

/-- **The zeta layer below the harmonic envelope.**  The whole dominant model
`-C exp(a x)/x` annihilates `q''²-4(q')³`, where `q=g'/g`.  The exact Gamma pole germ crosses that
envelope two factorial orders down, and the transverse coefficient is the nonzero zeta value
`-24 ζ(2)/x⁴ = -4π²/x⁴`. -/
theorem tendsto_gammaFactorialLogCurvatureDiscriminant_div_factorialScale_sq
    {x : ℂ} (hx : x ≠ 0) :
    Tendsto (fun n : ℕ =>
      gammaFactorialLogCurvatureDiscriminant n x /
        reciprocalGammaFactorialScale n ^ 2) atTop
      (𝓝 (-4 * (Real.pi : ℂ) ^ 2 / x ^ 4)) := by
  let s : ℕ → ℂ := reciprocalGammaFactorialScale
  let T : ℕ → ℂ := fun n => gammaFactorialScaledTrigamma n x
  let U : ℕ → ℂ := fun n => gammaFactorialScaledSecondPolygamma n x
  let T0 : ℂ := x⁻¹ ^ 2
  let U0 : ℂ := 2 * (-x)⁻¹ ^ 3
  have hs : Tendsto s atTop (𝓝 0) :=
    tendsto_reciprocalGammaFactorialScale_zero
  have hsne : ∀ n : ℕ, s n ≠ 0 := by
    intro n
    dsimp [s]
    exact div_ne_zero (pow_ne_zero _ (by norm_num))
      (by exact_mod_cast Nat.factorial_ne_zero n)
  have hTcor : Tendsto (fun n => (T n - T0) / s n ^ 2) atTop
      (𝓝 ((Real.pi : ℂ) ^ 2 / 3)) := by
    simpa [T, T0, s] using
      tendsto_gammaFactorialScaledTrigamma_div_factorialScale_sq hx
  have hUcor : Tendsto (fun n => (U n - U0) / s n ^ 2) atTop (𝓝 0) := by
    simpa [U, U0, s] using
      tendsto_gammaFactorialScaledSecondPolygamma_div_factorialScale_sq hx
  have hTdiff : Tendsto (fun n => T n - T0) atTop (𝓝 0) := by
    have h := hTcor.mul (hs.pow 2)
    have heq : ∀ n, (T n - T0) / s n ^ 2 * s n ^ 2 = T n - T0 := by
      intro n
      field_simp [hsne n]
    simpa using h.congr' (Filter.Eventually.of_forall heq)
  have hUdiff : Tendsto (fun n => U n - U0) atTop (𝓝 0) := by
    have h := hUcor.mul (hs.pow 2)
    have heq : ∀ n, (U n - U0) / s n ^ 2 * s n ^ 2 = U n - U0 := by
      intro n
      field_simp [hsne n]
    simpa using h.congr' (Filter.Eventually.of_forall heq)
  have hT : Tendsto T atTop (𝓝 T0) := by
    have h := hTdiff.add_const T0
    simpa [sub_add_cancel] using h
  have hU : Tendsto U atTop (𝓝 U0) := by
    have h := hUdiff.add_const U0
    simpa [sub_add_cancel] using h
  have hUfactor : Tendsto (fun n => U n + U0) atTop (𝓝 (2 * U0)) := by
    have h := hU.add_const U0
    have hvalue : U0 + U0 = 2 * U0 := by ring
    rw [hvalue] at h
    exact h
  have hTfactor : Tendsto (fun n => T n ^ 2 + T n * T0 + T0 ^ 2)
      atTop (𝓝 (3 * T0 ^ 2)) := by
    have h := ((hT.pow 2).add (hT.mul_const T0)).add_const (T0 ^ 2)
    have hvalue : T0 ^ 2 + T0 * T0 + T0 ^ 2 = 3 * T0 ^ 2 := by ring
    rw [hvalue] at h
    exact h
  have hUterm : Tendsto (fun n =>
      ((U n - U0) / s n ^ 2) * (U n + U0)) atTop (𝓝 0) := by
    simpa using hUcor.mul hUfactor
  have hTterm : Tendsto (fun n =>
      4 * ((T n - T0) / s n ^ 2) *
        (T n ^ 2 + T n * T0 + T0 ^ 2)) atTop
      (𝓝 (4 * (Real.pi : ℂ) ^ 2 * T0 ^ 2)) := by
    have h := (hTcor.mul hTfactor).const_mul 4
    convert h using 1
    · funext n
      ring
    · ring
  have hlimit : Tendsto (fun n =>
      ((U n - U0) / s n ^ 2) * (U n + U0) -
        4 * ((T n - T0) / s n ^ 2) *
          (T n ^ 2 + T n * T0 + T0 ^ 2)) atTop
      (𝓝 (-4 * (Real.pi : ℂ) ^ 2 * T0 ^ 2)) := by
    have h := hUterm.sub hTterm
    have hvalue : (0 : ℂ) - 4 * (Real.pi : ℂ) ^ 2 * T0 ^ 2 =
        -4 * (Real.pi : ℂ) ^ 2 * T0 ^ 2 := by ring
    rw [hvalue] at h
    exact h
  have heq : ∀ n,
      gammaFactorialLogCurvatureDiscriminant n x / s n ^ 2 =
        ((U n - U0) / s n ^ 2) * (U n + U0) -
          4 * ((T n - T0) / s n ^ 2) *
            (T n ^ 2 + T n * T0 + T0 ^ 2) := by
    intro n
    rw [gammaFactorialLogCurvatureDiscriminant]
    simp only [T, U]
    field_simp [hsne n]
    ring
  have hfinal := hlimit.congr' (Filter.Eventually.of_forall fun n => (heq n).symm)
  have hvalue : -4 * (Real.pi : ℂ) ^ 2 * T0 ^ 2 =
      -4 * (Real.pi : ℂ) ^ 2 / x ^ 4 := by
    dsimp [T0]
    field_simp [hx]
  rw [hvalue] at hfinal
  simpa [s] using hfinal

/-- A denominator-free third-order differential polynomial cutting out the
exponential-reciprocal envelope.  Writing `q=y'/y`, its two covariants are
`A=y²q'` and `B=y³q''`; this is `B²-4A³`. -/
def exponentialReciprocalJetDiscriminant (y0 y1 y2 y3 : ℂ) : ℂ :=
  (y0 ^ 2 * y3 - 3 * y0 * y1 * y2 + 2 * y1 ^ 3) ^ 2 -
    4 * (y0 * y2 - y1 ^ 2) ^ 3

theorem exponentialReciprocalJetDiscriminant_bell
    (g q T U : ℂ) :
    exponentialReciprocalJetDiscriminant g (g * q)
        (g * (q ^ 2 + T)) (g * (q ^ 3 + 3 * q * T + U)) =
      g ^ 6 * (U ^ 2 - 4 * T ^ 3) := by
  rw [exponentialReciprocalJetDiscriminant]
  ring

def gammaFactorialExponentialEnvelopeDefect (n : ℕ) (x : ℂ) : ℂ :=
  exponentialReciprocalJetDiscriminant
    (factorialBlowUpZoom Complex.Gamma n x)
    (iteratedDeriv 1 (factorialBlowUpZoom Complex.Gamma n) x)
    (iteratedDeriv 2 (factorialBlowUpZoom Complex.Gamma n) x)
    (iteratedDeriv 3 (factorialBlowUpZoom Complex.Gamma n) x)

theorem gammaFactorialExponentialEnvelopeDefect_eq
    (n : ℕ) (x : ℂ)
    (hpole : ∀ k : ℕ,
      -(n : ℂ) + reciprocalGammaFactorialScale n * x ≠ -(k : ℂ)) :
    gammaFactorialExponentialEnvelopeDefect n x =
      factorialBlowUpZoom Complex.Gamma n x ^ 6 *
        gammaFactorialLogCurvatureDiscriminant n x := by
  let w : ℂ := -(n : ℂ) + reciprocalGammaFactorialScale n * x
  have hBell2 := iteratedDeriv_two_Gamma_eq_logDeriv w hpole
  have hBell3 := iteratedDeriv_three_Gamma_eq_logDeriv w hpole
  have hpsi : (fun z => deriv Complex.Gamma z / Complex.Gamma z) =
      Complex.digamma := by
    funext z
    rw [Complex.digamma_def, logDeriv_apply]
  have hratio : deriv Complex.Gamma w / Complex.Gamma w = Complex.digamma w := by
    rw [Complex.digamma_def, logDeriv_apply]
  have hGamma : Complex.Gamma w ≠ 0 := Complex.Gamma_ne_zero hpole
  have hderiv : deriv Complex.Gamma w = Complex.digamma w * Complex.Gamma w :=
    (div_eq_iff hGamma).mp hratio
  have hiter : iteratedDeriv 2 Complex.digamma w =
      deriv (deriv Complex.digamma) w := by
    rw [show (2 : ℕ) = 1 + 1 by omega, iteratedDeriv_succ, iteratedDeriv_one]
  rw [gammaFactorialExponentialEnvelopeDefect,
    iteratedDeriv_factorialBlowUpZoom,
    iteratedDeriv_factorialBlowUpZoom,
    iteratedDeriv_factorialBlowUpZoom]
  rw [show iteratedDeriv 2 Complex.Gamma w = _ from hBell2]
  rw [show iteratedDeriv 3 Complex.Gamma w = _ from hBell3]
  rw [hpsi]
  simp only [factorialBlowUpZoom, gammaFactorialLogCurvatureDiscriminant,
    gammaFactorialScaledTrigamma, gammaFactorialScaledSecondPolygamma,
    iteratedDeriv_one, pow_one]
  dsimp only [w] at hratio hderiv hiter
  rw [hratio, hderiv, hiter]
  rw [exponentialReciprocalJetDiscriminant]
  ring

/-- **Denominator-free escape from the complete exponential-reciprocal envelope.**  The exact
Gamma third jet crosses the common differential hypersurface of `-C exp(a x)/x` at scale `sₙ²`,
with nonzero transverse profile `-4π²/x¹⁰`. -/
theorem tendsto_gammaFactorialExponentialEnvelopeDefect_div_factorialScale_sq
    {x : ℂ} (hx : x ≠ 0) :
    Tendsto (fun n : ℕ =>
      gammaFactorialExponentialEnvelopeDefect n x /
        reciprocalGammaFactorialScale n ^ 2) atTop
      (𝓝 (-4 * (Real.pi : ℂ) ^ 2 / x ^ 10)) := by
  let g : ℕ → ℂ := fun n => factorialBlowUpZoom Complex.Gamma n x
  let M : ℂ := (-x)⁻¹
  let a : ℕ → ℂ := gammaHarmonicMicroscopeScale
  have ha0 : Tendsto a atTop (𝓝 0) := tendsto_gammaHarmonicMicroscopeScale_zero
  have hane : ∀ᶠ n : ℕ in atTop, a n ≠ 0 := by
    filter_upwards [Filter.eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
    exact gammaHarmonicMicroscopeScale_ne_zero hn
  have hgcor : Tendsto (fun n => (g n - M) / a n) atTop (𝓝 (-1)) := by
    simpa [g, M, a] using tendsto_gammaFactorialZoom_first_harmonic hx
  have hgdiff : Tendsto (fun n => g n - M) atTop (𝓝 0) := by
    have h := hgcor.mul ha0
    have heq : ∀ᶠ n in atTop, (g n - M) / a n * a n = g n - M := by
      filter_upwards [hane] with n hn
      field_simp [hn]
    simpa using h.congr' heq
  have hg : Tendsto g atTop (𝓝 M) := by
    have h := hgdiff.add_const M
    simpa [sub_add_cancel] using h
  have hlog := tendsto_gammaFactorialLogCurvatureDiscriminant_div_factorialScale_sq hx
  have hproduct := (hg.pow 6).mul hlog
  have hsx : Tendsto (fun n : ℕ => reciprocalGammaFactorialScale n * x)
      atTop (𝓝 0) := by
    simpa using tendsto_reciprocalGammaFactorialScale_zero.mul_const x
  have hsmall : ∀ᶠ n : ℕ in atTop,
      ‖reciprocalGammaFactorialScale n * x‖ < 1 :=
    hsx.norm.eventually_lt_const (by norm_num)
  have hregular : ∀ᶠ n : ℕ in atTop, ∀ k : ℕ,
      -(n : ℂ) + reciprocalGammaFactorialScale n * x ≠ -(k : ℂ) := by
    filter_upwards [hsmall] with n hn k
    let z : ℂ := reciprocalGammaFactorialScale n * x
    have hs : reciprocalGammaFactorialScale n ≠ 0 :=
      div_ne_zero (pow_ne_zero _ (by norm_num))
        (by exact_mod_cast Nat.factorial_ne_zero n)
    have hz : z ≠ 0 := mul_ne_zero hs hx
    have hzInt : ∀ m : ℤ, z ≠ (m : ℂ) :=
      ne_intCast_of_ne_zero_of_norm_lt_one hz (by simpa [z] using hn)
    intro hpole
    apply hzInt ((n : ℤ) - (k : ℤ))
    dsimp [z]
    push_cast
    linear_combination hpole
  have heq : ∀ᶠ n : ℕ in atTop,
      gammaFactorialExponentialEnvelopeDefect n x /
          reciprocalGammaFactorialScale n ^ 2 =
        g n ^ 6 *
          (gammaFactorialLogCurvatureDiscriminant n x /
            reciprocalGammaFactorialScale n ^ 2) := by
    filter_upwards [hregular] with n hn
    rw [gammaFactorialExponentialEnvelopeDefect_eq n x hn]
    simp only [g]
    ring
  have hfinal := hproduct.congr' (heq.mono fun _ h => h.symm)
  have hvalue : M ^ 6 * (-4 * (Real.pi : ℂ) ^ 2 / x ^ 4) =
      -4 * (Real.pi : ℂ) ^ 2 / x ^ 10 := by
    dsimp [M]
    field_simp [hx]
  rw [hvalue] at hfinal
  exact hfinal

end

end GaloisForLFunctions
