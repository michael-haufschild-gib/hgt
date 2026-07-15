import GaloisForLFunctions.HTGeometry.GammaFactorialSecondJetHarmonicResidue

/-!
# Third-jet projective residue of the factorial Gamma zoom

The reciprocal boundary profile `M(x) = -1/x` annihilates the translation-invariant Schwarzian
numerator `2 M' M''' - 3 (M'')²`.  In contrast with the second-jet projective curvature, its
linear harmonic correction also cancels.  This file resolves the next asymptotic layer: the exact
Gamma zoom crosses the Schwarzian hypersurface at the *quadratic* harmonic scale, with residue
`-6/x⁴`.

The proof derives the required second-order trigamma and second-polygamma controls from exact
negative-integer shift formulae; no numerical approximation enters the argument.
-/

namespace GaloisForLFunctions

open Complex Filter Topology

noncomputable section

/-- The scaled trigamma has no correction at quadratic harmonic order. -/
theorem tendsto_gammaFactorialScaledTrigamma_second_harmonic
    {x : ℂ} (hx : x ≠ 0) :
    Tendsto (fun n : ℕ =>
      (gammaFactorialScaledTrigamma n x - x⁻¹ ^ 2) /
        gammaHarmonicMicroscopeScale n ^ 2) atTop (𝓝 0) := by
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
  have hpsi : Tendsto (fun n => iteratedDeriv 1 Complex.digamma (1 + z n))
      atTop (𝓝 (iteratedDeriv 1 Complex.digamma 1)) :=
    (analyticAt_iteratedDeriv_of_analyticAt (analyticAt_digamma_of_offPoles hOff1) 1).continuousAt.tendsto.comp
      hinput
  have hH2 : Tendsto (fun n => (harmonic n : ℂ)⁻¹ ^ 2) atTop (𝓝 0) := by
    simpa using tendsto_inv_harmonic_cast_complex_zero.pow 2
  have hlocal : Tendsto (fun n =>
      (harmonic n : ℂ)⁻¹ ^ 2 * iteratedDeriv 1 Complex.digamma (1 + z n))
      atTop (𝓝 0) := by
    simpa using hH2.mul hpsi
  have hsmall : ∀ᶠ n : ℕ in atTop, ‖z n‖ ≤ 1 / 2 :=
    (hz.norm.eventually_lt_const (by norm_num)).mono fun _ h => h.le
  have hsum : Tendsto (fun n =>
      (harmonic n : ℂ)⁻¹ ^ 2 * shiftedHarmonicSquareSum n (z n))
      atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hmajor : Tendsto (fun n => 4 * ‖(harmonic n : ℂ)⁻¹‖)
        atTop (𝓝 0) := by
      simpa using tendsto_inv_harmonic_cast_complex_zero.norm.const_mul 4
    apply squeeze_zero' (Filter.Eventually.of_forall fun n => norm_nonneg _) _ hmajor
    filter_upwards [hsmall, Filter.eventually_atTop.2 ⟨1, fun n hn => hn⟩]
      with n hzn hn
    have hHreal : 0 < (harmonic n : ℝ) := by
      exact_mod_cast harmonic_pos (by omega : n ≠ 0)
    have hbound := norm_shiftedHarmonicSquareSum_le hzn n
    have hnormH : ‖(harmonic n : ℂ)‖ = (harmonic n : ℝ) := by
      rw [show (harmonic n : ℂ) = ((harmonic n : ℝ) : ℂ) by norm_cast]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hHreal]
    rw [norm_mul, norm_pow]
    have hinvnorm : ‖(harmonic n : ℂ)⁻¹‖ = (harmonic n : ℝ)⁻¹ := by
      rw [norm_inv, hnormH]
    rw [hinvnorm]
    calc
      (harmonic n : ℝ)⁻¹ ^ 2 * ‖shiftedHarmonicSquareSum n (z n)‖ ≤
          (harmonic n : ℝ)⁻¹ ^ 2 * (4 * (harmonic n : ℝ)) := by gcongr
      _ = 4 * (harmonic n : ℝ)⁻¹ := by field_simp [hHreal.ne']
  have hlimit := hlocal.add hsum
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
      (gammaFactorialScaledTrigamma n x - x⁻¹ ^ 2) /
          gammaHarmonicMicroscopeScale n ^ 2 =
        (harmonic n : ℂ)⁻¹ ^ 2 *
          (iteratedDeriv 1 Complex.digamma (1 + z n) +
            shiftedHarmonicSquareSum n (z n)) := by
    filter_upwards [hregular, Filter.eventually_atTop.2 ⟨1, fun n hn => hn⟩]
      with n hzn hn
    have hsn : s n ≠ 0 := by
      dsimp [s]
      exact div_ne_zero (pow_ne_zero _ (by norm_num))
        (by exact_mod_cast Nat.factorial_ne_zero n)
    have hH : (harmonic n : ℂ) ≠ 0 := by
      exact_mod_cast (harmonic_pos (by omega : n ≠ 0)).ne'
    have hformula := iteratedDeriv_one_digamma_neg_nat_add_of_ne_int (z n) hzn n
    rw [gammaFactorialScaledTrigamma, gammaHarmonicMicroscopeScale]
    change (s n ^ 2 * iteratedDeriv 1 Complex.digamma (-↑n + z n) - x⁻¹ ^ 2) /
      (s n * (harmonic n : ℂ)) ^ 2 = _
    rw [hformula]
    dsimp [z]
    field_simp [hsn, hH, hx]
    ring
  have hcombined : Tendsto (fun n =>
      (harmonic n : ℂ)⁻¹ ^ 2 *
        (iteratedDeriv 1 Complex.digamma (1 + z n) +
          shiftedHarmonicSquareSum n (z n))) atTop (𝓝 0) := by
    convert hlimit using 1 <;> ring
  exact hcombined.congr' (heq.mono fun _ h => h.symm)

/-- Cubic shifted harmonic tail arising from the order-two differentiated digamma recurrence. -/
def shiftedHarmonicCubeSum (n : ℕ) (z : ℂ) : ℂ :=
  ∑ j ∈ Finset.range n, ((((j + 1 : ℕ) : ℂ) - z) ^ 3)⁻¹

theorem iteratedDeriv_two_digamma_neg_nat_add_of_ne_int (z : ℂ)
    (hz : ∀ k : ℤ, z ≠ (k : ℂ)) (n : ℕ) :
    iteratedDeriv 2 Complex.digamma (-(n : ℂ) + z) =
      iteratedDeriv 2 Complex.digamma (1 + z) - 2 * z⁻¹ ^ 3 +
        2 * shiftedHarmonicCubeSum n z := by
  induction n with
  | zero =>
      have hzOff : ∀ k : ℕ, z ≠ -(k : ℂ) := by
        intro k
        simpa using hz (-(k : ℤ))
      have hstep := digammaJet_shift 2 hzOff
      simp only [Nat.cast_zero, neg_zero, zero_add, shiftedHarmonicCubeSum,
        Finset.range_zero, Finset.sum_empty, mul_zero, add_zero]
      rw [show (1 + z : ℂ) = z + 1 by ring, hstep]
      have hz0 : z ≠ 0 := by simpa using hz 0
      norm_num
      field_simp [hz0]
      ring
  | succ n ih =>
      let w : ℂ := -((n + 1 : ℕ) : ℂ) + z
      have hw : ∀ k : ℕ, w ≠ -(k : ℂ) := by
        intro k hwk
        apply hz ((n : ℤ) + 1 - (k : ℤ))
        dsimp [w] at hwk
        norm_num [Int.cast_sub, Int.cast_add]
        push_cast at hwk ⊢
        linear_combination hwk
      have hstep := digammaJet_shift 2 hw
      have hwadd : w + 1 = -(n : ℂ) + z := by
        dsimp [w]
        push_cast
        ring
      have hwcube : w ^ 3 = -((((n + 1 : ℕ) : ℂ) - z) ^ 3) := by
        dsimp [w]
        ring
      change iteratedDeriv 2 Complex.digamma w = _
      have hsolve : iteratedDeriv 2 Complex.digamma w =
          iteratedDeriv 2 Complex.digamma (w + 1) - 2 * (w ^ 3)⁻¹ := by
        rw [hstep]
        norm_num
        ring
      rw [hsolve, hwadd, ih]
      simp only [shiftedHarmonicCubeSum, Finset.sum_range_succ, hwcube, inv_neg]
      ring

theorem norm_shiftedHarmonicCubeSum_le {z : ℂ}
    (hz : ‖z‖ ≤ 1 / 2) (n : ℕ) :
    ‖shiftedHarmonicCubeSum n z‖ ≤ 8 * (harmonic n : ℝ) := by
  rw [shiftedHarmonicCubeSum]
  calc
    ‖∑ j ∈ Finset.range n, ((((j + 1 : ℕ) : ℂ) - z) ^ 3)⁻¹‖ ≤
        ∑ j ∈ Finset.range n, ‖((((j + 1 : ℕ) : ℂ) - z) ^ 3)⁻¹‖ :=
      norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range n, 8 / ((j + 1 : ℕ) : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [← inv_pow, norm_pow]
      have h := norm_shiftedInverse_le hz j
      have hk : 1 ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le j)
      have hnon : 0 ≤ ‖(((j + 1 : ℕ) : ℂ) - z)⁻¹‖ := norm_nonneg _
      calc
        ‖(↑(j + 1) - z)⁻¹‖ ^ 3 ≤ (2 / ((j + 1 : ℕ) : ℝ)) ^ 3 := by
          gcongr
        _ ≤ 8 / ((j + 1 : ℕ) : ℝ) := by
          have hkpos : 0 < ((j + 1 : ℕ) : ℝ) := lt_of_lt_of_le zero_lt_one hk
          field_simp [hkpos.ne']
          nlinarith
    _ = 8 * (harmonic n : ℝ) := by
      rw [harmonic]
      push_cast
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      field_simp

/-- The order-two polygamma in the factorial microscope coordinates. -/
def gammaFactorialScaledSecondPolygamma (n : ℕ) (x : ℂ) : ℂ :=
  reciprocalGammaFactorialScale n ^ 3 *
    iteratedDeriv 2 Complex.digamma
      (-(n : ℂ) + reciprocalGammaFactorialScale n * x)

/-- The scaled order-two polygamma has no correction at quadratic harmonic order. -/
theorem tendsto_gammaFactorialScaledSecondPolygamma_second_harmonic
    {x : ℂ} (hx : x ≠ 0) :
    Tendsto (fun n : ℕ =>
      (gammaFactorialScaledSecondPolygamma n x - 2 * (-x)⁻¹ ^ 3) /
        gammaHarmonicMicroscopeScale n ^ 2) atTop (𝓝 0) := by
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
    (analyticAt_iteratedDeriv_of_analyticAt (analyticAt_digamma_of_offPoles hOff1) 2).continuousAt.tendsto.comp
      hinput
  have hsdivH2 : Tendsto (fun n =>
      s n * (harmonic n : ℂ)⁻¹ ^ 2) atTop (𝓝 0) := by
    simpa using hs.mul (tendsto_inv_harmonic_cast_complex_zero.pow 2)
  have hlocal : Tendsto (fun n =>
      (s n * (harmonic n : ℂ)⁻¹ ^ 2) *
        iteratedDeriv 2 Complex.digamma (1 + z n)) atTop (𝓝 0) := by
    simpa using hsdivH2.mul hpsi
  have hsmall : ∀ᶠ n : ℕ in atTop, ‖z n‖ ≤ 1 / 2 :=
    (hz.norm.eventually_lt_const (by norm_num)).mono fun _ h => h.le
  have hsum : Tendsto (fun n =>
      (s n * (harmonic n : ℂ)⁻¹ ^ 2) *
        (2 * shiftedHarmonicCubeSum n (z n))) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hmajor : Tendsto (fun n =>
        16 * (‖s n‖ * ‖(harmonic n : ℂ)⁻¹‖)) atTop (𝓝 0) := by
      simpa using (hs.norm.mul tendsto_inv_harmonic_cast_complex_zero.norm).const_mul 16
    apply squeeze_zero' (Filter.Eventually.of_forall fun n => norm_nonneg _) _ hmajor
    filter_upwards [hsmall, Filter.eventually_atTop.2 ⟨1, fun n hn => hn⟩]
      with n hzn hn
    have hHreal : 0 < (harmonic n : ℝ) := by
      exact_mod_cast harmonic_pos (by omega : n ≠ 0)
    have hbound := norm_shiftedHarmonicCubeSum_le hzn n
    have hnormH : ‖(harmonic n : ℂ)‖ = (harmonic n : ℝ) := by
      rw [show (harmonic n : ℂ) = ((harmonic n : ℝ) : ℂ) by norm_cast]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hHreal]
    have hinvnorm : ‖(harmonic n : ℂ)⁻¹‖ = (harmonic n : ℝ)⁻¹ := by
      rw [norm_inv, hnormH]
    rw [norm_mul, norm_mul, norm_pow, hinvnorm, norm_mul]
    norm_num
    calc
      ‖s n‖ * ((harmonic n : ℝ) ^ 2)⁻¹ *
          (2 * ‖shiftedHarmonicCubeSum n (z n)‖) ≤
        ‖s n‖ * ((harmonic n : ℝ) ^ 2)⁻¹ *
          (2 * (8 * (harmonic n : ℝ))) := by gcongr
      _ = 16 * (‖s n‖ * (harmonic n : ℝ)⁻¹) := by
        field_simp [hHreal.ne']
        ring
  have hlimit := hlocal.add hsum
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
          gammaHarmonicMicroscopeScale n ^ 2 =
        (s n * (harmonic n : ℂ)⁻¹ ^ 2) *
          (iteratedDeriv 2 Complex.digamma (1 + z n) +
            2 * shiftedHarmonicCubeSum n (z n)) := by
    filter_upwards [hregular, Filter.eventually_atTop.2 ⟨1, fun n hn => hn⟩]
      with n hzn hn
    have hsn : s n ≠ 0 := by
      dsimp [s]
      exact div_ne_zero (pow_ne_zero _ (by norm_num))
        (by exact_mod_cast Nat.factorial_ne_zero n)
    have hH : (harmonic n : ℂ) ≠ 0 := by
      exact_mod_cast (harmonic_pos (by omega : n ≠ 0)).ne'
    have hformula := iteratedDeriv_two_digamma_neg_nat_add_of_ne_int (z n) hzn n
    rw [gammaFactorialScaledSecondPolygamma, gammaHarmonicMicroscopeScale]
    change (s n ^ 3 * iteratedDeriv 2 Complex.digamma (-↑n + z n) -
        2 * (-x)⁻¹ ^ 3) / (s n * (harmonic n : ℂ)) ^ 2 = _
    rw [hformula]
    dsimp [z]
    field_simp [hsn, hH, hx]
    ring
  have hcombined : Tendsto (fun n =>
      (s n * (harmonic n : ℂ)⁻¹ ^ 2) *
        (iteratedDeriv 2 Complex.digamma (1 + z n) +
          2 * shiftedHarmonicCubeSum n (z n))) atTop (𝓝 0) := by
    convert hlimit using 1 <;> ring
  exact hcombined.congr' (heq.mono fun _ h => h.symm)

/-- The translation-invariant Schwarzian numerator of the factorial Gamma zoom. -/
def gammaFactorialThirdJetProjectiveDefect (n : ℕ) (x : ℂ) : ℂ :=
  2 * iteratedDeriv 1 (factorialBlowUpZoom Complex.Gamma n) x *
      iteratedDeriv 3 (factorialBlowUpZoom Complex.Gamma n) x -
    3 * iteratedDeriv 2 (factorialBlowUpZoom Complex.Gamma n) x ^ 2

theorem gammaFactorialThirdJetProjectiveDefect_eq
    (n : ℕ) (x : ℂ)
    (hpole : ∀ k : ℕ,
      -(n : ℂ) + reciprocalGammaFactorialScale n * x ≠ -(k : ℂ)) :
    gammaFactorialThirdJetProjectiveDefect n x =
      factorialBlowUpZoom Complex.Gamma n x ^ 2 *
        (2 * gammaFactorialScaledDigamma n x *
            gammaFactorialScaledSecondPolygamma n x -
          3 * gammaFactorialScaledTrigamma n x ^ 2 -
          gammaFactorialScaledDigamma n x ^ 4) := by
  let w : ℂ := -(n : ℂ) + reciprocalGammaFactorialScale n * x
  have hBell2 := iteratedDeriv_two_Gamma_eq_logDeriv w hpole
  have hBell3 := iteratedDeriv_three_Gamma_eq_logDeriv w hpole
  have hpsi : (fun z => deriv Complex.Gamma z / Complex.Gamma z) =
      Complex.digamma := by
    funext z
    rw [Complex.digamma_def, logDeriv_apply]
  rw [gammaFactorialThirdJetProjectiveDefect,
    iteratedDeriv_factorialBlowUpZoom,
    iteratedDeriv_factorialBlowUpZoom,
    iteratedDeriv_factorialBlowUpZoom]
  rw [show iteratedDeriv 2 Complex.Gamma w = _ from hBell2]
  rw [show iteratedDeriv 3 Complex.Gamma w = _ from hBell3]
  rw [hpsi]
  simp only [factorialBlowUpZoom, gammaFactorialScaledDigamma,
    gammaFactorialScaledTrigamma, gammaFactorialScaledSecondPolygamma,
    iteratedDeriv_one, pow_one]
  have hratio : deriv Complex.Gamma w / Complex.Gamma w = Complex.digamma w := by
    rw [Complex.digamma_def, logDeriv_apply]
  have hGamma : Complex.Gamma w ≠ 0 := Complex.Gamma_ne_zero hpole
  have hderiv : deriv Complex.Gamma w = Complex.digamma w * Complex.Gamma w :=
    (div_eq_iff hGamma).mp hratio
  have hiter : iteratedDeriv 2 Complex.digamma w =
      deriv (deriv Complex.digamma) w := by
    rw [show (2 : ℕ) = 1 + 1 by omega, iteratedDeriv_succ, iteratedDeriv_one]
  dsimp only [w] at hratio hderiv hiter
  rw [hratio]
  rw [hderiv, hiter]
  ring

/-- **Quadratic Schwarzian residue.**  Although both the reciprocal boundary and the first
harmonic correction lie in the Schwarzian hypersurface, the exact Gamma zoom leaves it at the
quadratic harmonic scale, with the nonzero profile `-6/x⁴`. -/
theorem tendsto_gammaFactorialThirdJetProjectiveDefect_div_harmonicScale_sq
    {x : ℂ} (hx : x ≠ 0) :
    Tendsto (fun n : ℕ =>
      gammaFactorialThirdJetProjectiveDefect n x /
        gammaHarmonicMicroscopeScale n ^ 2) atTop (𝓝 (-6 / x ^ 4)) := by
  let g : ℕ → ℂ := fun n => factorialBlowUpZoom Complex.Gamma n x
  let q : ℕ → ℂ := fun n => gammaFactorialScaledDigamma n x
  let T : ℕ → ℂ := fun n => gammaFactorialScaledTrigamma n x
  let U : ℕ → ℂ := fun n => gammaFactorialScaledSecondPolygamma n x
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
  have hqcor : Tendsto (fun n => (q n - M) / a n) atTop (𝓝 1) := by
    simpa [q, M, a, sub_eq_add_neg] using
      tendsto_gammaFactorialScaledDigamma_first_harmonic hx
  have hqdiff : Tendsto (fun n => q n - M) atTop (𝓝 0) := by
    have h := hqcor.mul ha0
    have heq : ∀ᶠ n in atTop, (q n - M) / a n * a n = q n - M := by
      filter_upwards [hane] with n hn
      field_simp [hn]
    simpa using h.congr' heq
  have hq : Tendsto q atTop (𝓝 M) := by
    have h := hqdiff.add_const M
    simpa [sub_add_cancel] using h
  have hT2 : Tendsto (fun n => (T n - M ^ 2) / a n ^ 2) atTop (𝓝 0) := by
    simpa [T, M, a] using tendsto_gammaFactorialScaledTrigamma_second_harmonic hx
  have hTdiff : Tendsto (fun n => T n - M ^ 2) atTop (𝓝 0) := by
    have h := hT2.mul (ha0.pow 2)
    have heq : ∀ᶠ n in atTop,
        (T n - M ^ 2) / a n ^ 2 * a n ^ 2 = T n - M ^ 2 := by
      filter_upwards [hane] with n hn
      field_simp [hn]
    simpa using h.congr' heq
  have hT : Tendsto T atTop (𝓝 (M ^ 2)) := by
    have h := hTdiff.add_const (M ^ 2)
    simpa [sub_add_cancel] using h
  have hU2 : Tendsto (fun n => (U n - 2 * M ^ 3) / a n ^ 2) atTop (𝓝 0) := by
    simpa [U, M, a] using
      tendsto_gammaFactorialScaledSecondPolygamma_second_harmonic hx
  have hfactor : Tendsto (fun n => q n ^ 2 + 2 * q n * M + 3 * M ^ 2)
      atTop (𝓝 (6 * M ^ 2)) := by
    have h := ((hq.pow 2).add ((hq.mul_const M).const_mul 2)).add_const
      (3 * M ^ 2)
    convert h using 1
    · funext n
      ring
    · ring
  have hqrem : Tendsto (fun n =>
      (q n ^ 4 - M ^ 4 - 4 * M ^ 3 * (q n - M)) / a n ^ 2)
      atTop (𝓝 (6 * M ^ 2)) := by
    have h := (hqcor.pow 2).mul hfactor
    have heq : ∀ᶠ n in atTop,
        ((q n - M) / a n) ^ 2 *
          (q n ^ 2 + 2 * q n * M + 3 * M ^ 2) =
        (q n ^ 4 - M ^ 4 - 4 * M ^ 3 * (q n - M)) / a n ^ 2 := by
      filter_upwards [hane] with n hn
      field_simp [hn]
      ring
    simpa using h.congr' heq
  have hUterm : Tendsto (fun n =>
      2 * q n * ((U n - 2 * M ^ 3) / a n ^ 2)) atTop (𝓝 0) := by
    simpa only [mul_assoc, mul_zero] using (hq.mul hU2).const_mul 2
  have hTterm : Tendsto (fun n =>
      3 * ((T n - M ^ 2) / a n ^ 2) * (T n + M ^ 2)) atTop (𝓝 0) := by
    simpa only [mul_assoc, zero_mul, mul_zero] using
      (hT2.mul (hT.add_const (M ^ 2))).const_mul 3
  have hbracket : Tendsto (fun n =>
      (2 * q n * U n - 3 * T n ^ 2 - q n ^ 4) / a n ^ 2)
      atTop (𝓝 (-6 * M ^ 2)) := by
    have h := (hUterm.sub hTterm).sub hqrem
    have heq : ∀ᶠ n in atTop,
        2 * q n * ((U n - 2 * M ^ 3) / a n ^ 2) -
            3 * ((T n - M ^ 2) / a n ^ 2) * (T n + M ^ 2) -
            (q n ^ 4 - M ^ 4 - 4 * M ^ 3 * (q n - M)) / a n ^ 2 =
          (2 * q n * U n - 3 * T n ^ 2 - q n ^ 4) / a n ^ 2 := by
      filter_upwards [hane] with n hn
      field_simp [hn]
      ring
    convert h.congr' heq using 1 <;> ring
  have hproduct := (hg.pow 2).mul hbracket
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
      gammaFactorialThirdJetProjectiveDefect n x / a n ^ 2 =
        g n ^ 2 * ((2 * q n * U n - 3 * T n ^ 2 - q n ^ 4) / a n ^ 2) := by
    filter_upwards [hregular] with n hn
    rw [gammaFactorialThirdJetProjectiveDefect_eq n x hn]
    simp only [g, q, T, U]
    ring
  have hfinal := hproduct.congr' (heq.mono fun _ h => h.symm)
  have hlimval : M ^ 2 * (-6 * M ^ 2) = -6 / x ^ 4 := by
    dsimp [M]
    field_simp [hx]
  rw [hlimval] at hfinal
  simpa [a] using hfinal

end

end GaloisForLFunctions
