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


/-- Cubic shifted harmonic tail arising from the order-two differentiated digamma recurrence. -/
def shiftedHarmonicCubeSum (n : ℕ) (z : ℂ) : ℂ :=
  ∑ j ∈ Finset.range n, ((((j + 1 : ℕ) : ℂ) - z) ^ 3)⁻¹

theorem iteratedDeriv_two_digamma_neg_nat_add_of_ne_int (z : ℂ)
    (hz : ∀ k : ℤ, z ≠ (k : ℂ)) (n : ℕ) :
    iteratedDeriv 2 Complex.digamma (-(n : ℂ) + z) =
      iteratedDeriv 2 Complex.digamma (1 + z) - 2 * z⁻¹ ^ 3 +
        2 * shiftedHarmonicCubeSum n z := by
  have h := iteratedDeriv_digamma_neg_nat_add_of_ne_int 2 z hz n
  simp only [shiftedHarmonicCubeSum, shiftedHarmonicPowerSum, Nat.factorial, inv_pow] at h ⊢
  push_cast at h ⊢
  linear_combination h

theorem norm_shiftedHarmonicCubeSum_le {z : ℂ}
    (hz : ‖z‖ ≤ 1 / 2) (n : ℕ) :
    ‖shiftedHarmonicCubeSum n z‖ ≤ 8 * (harmonic n : ℝ) := by
  simpa [shiftedHarmonicCubeSum, shiftedHarmonicPowerSum,
    show ((2 : ℝ)) ^ 3 = 8 from by norm_num] using
    norm_shiftedHarmonicPowerSum_le hz (p := 3) (by norm_num) n

/-- The order-two polygamma in the factorial microscope coordinates. -/
def gammaFactorialScaledSecondPolygamma (n : ℕ) (x : ℂ) : ℂ :=
  reciprocalGammaFactorialScale n ^ 3 *
    iteratedDeriv 2 Complex.digamma
      (-(n : ℂ) + reciprocalGammaFactorialScale n * x)


/-- The order-two polygamma scaling is the order-`2` member of the indexed family. -/
theorem gammaFactorialScaledSecondPolygamma_eq_polygamma (n : ℕ) (x : ℂ) :
    gammaFactorialScaledSecondPolygamma n x = gammaFactorialScaledPolygamma 2 n x := rfl

/-- The scale power exactly cancels the scaled pole: `sʲ (s x)^{-j} = x^{-j}`. -/
private theorem scale_pow_mul_inv_pow {s x : ℂ} (hs : s ≠ 0) (j : ℕ) :
    s ^ j * (s * x)⁻¹ ^ j = x⁻¹ ^ j := by
  rw [mul_inv, mul_pow, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hs, one_pow, one_mul]

/-- A power of the reciprocal factorial scale times the squared inverse harmonic number vanishes,
for every exponent — including `0`, where the scale factor is `1` and the harmonic factor does all
the work. -/
private theorem tendsto_scale_pow_mul_inv_harmonic_pow (m : ℕ) {j : ℕ} (hj : 0 < j) :
    Tendsto (fun n : ℕ =>
      reciprocalGammaFactorialScale n ^ m * (harmonic n : ℂ)⁻¹ ^ j) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hmaj : Tendsto (fun n : ℕ => ‖(harmonic n : ℂ)⁻¹ ^ j‖) atTop (𝓝 0) := by
    simpa [zero_pow hj.ne'] using (tendsto_inv_harmonic_cast_complex_zero.pow j).norm
  have hsnorm : Tendsto (fun n : ℕ => ‖reciprocalGammaFactorialScale n‖) atTop (𝓝 0) := by
    simpa using tendsto_reciprocalGammaFactorialScale_zero.norm
  have hsb : ∀ᶠ n : ℕ in atTop, ‖reciprocalGammaFactorialScale n‖ ≤ 1 :=
    hsnorm.eventually_le_const (by norm_num : (0 : ℝ) < 1)
  apply squeeze_zero' (Filter.Eventually.of_forall fun n => norm_nonneg _) _ hmaj
  filter_upwards [hsb] with n hn
  rw [norm_mul, norm_pow]
  exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hn)


/-- **Order-indexed second-harmonic vanishing.**  After subtracting its principal pole term
`(-1)^{m+2} (m+1)! x^{-(m+2)}`, the scaled order-`(m+1)` polygamma has no correction at quadratic
harmonic order.  The pole cancels exactly because `z = s x` gives `s^{m+2} z^{-(m+2)} = x^{-(m+2)}`,
and what remains carries `s^m` — the scale exponent is one less than the jet order, which is why the
trigamma case (`m = 0`) shows no scale factor at all. -/
theorem tendsto_gammaFactorialScaledPolygamma_second_harmonic (m : ℕ) {x : ℂ} (hx : x ≠ 0) :
    Tendsto (fun n : ℕ =>
      (gammaFactorialScaledPolygamma (m + 1) n x -
          (-1) ^ (m + 2) * (((m + 1).factorial : ℕ) : ℂ) * x⁻¹ ^ (m + 2)) /
        gammaHarmonicMicroscopeScale n ^ 2) atTop (𝓝 0) := by
  let s : ℕ → ℂ := reciprocalGammaFactorialScale
  let z : ℕ → ℂ := fun n => s n * x
  have hs : Tendsto s atTop (𝓝 0) := tendsto_reciprocalGammaFactorialScale_zero
  have hz : Tendsto z atTop (𝓝 0) := by simpa [z] using hs.mul_const x
  have hinput : Tendsto (fun n => 1 + z n) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds.add hz :
      Tendsto (fun n => 1 + z n) atTop (𝓝 (1 + 0)))
  have hOff1 : ∀ j : ℕ, (1 : ℂ) ≠ -(j : ℂ) := by
    intro j hj
    have hre := congrArg Complex.re hj
    simp only [Complex.one_re, Complex.neg_re, Complex.natCast_re] at hre
    linarith [Nat.cast_nonneg (α := ℝ) j]
  have hpsi : Tendsto (fun n => iteratedDeriv (m + 1) Complex.digamma (1 + z n))
      atTop (𝓝 (iteratedDeriv (m + 1) Complex.digamma 1)) :=
    (analyticAt_iteratedDeriv_of_analyticAt (analyticAt_digamma_of_offPoles hOff1)
      (m + 1)).continuousAt.tendsto.comp hinput
  have hlocal : Tendsto (fun n : ℕ =>
      (s n ^ m * (harmonic n : ℂ)⁻¹ ^ 2) *
        iteratedDeriv (m + 1) Complex.digamma (1 + z n)) atTop (𝓝 0) := by
    simpa using
      (tendsto_scale_pow_mul_inv_harmonic_pow m (by norm_num : 0 < 2)).mul hpsi
  have hsmall : ∀ᶠ n : ℕ in atTop, ‖z n‖ ≤ 1 / 2 :=
    (hz.norm.eventually_lt_const (by norm_num)).mono fun _ h => h.le
  have hsum : Tendsto (fun n : ℕ =>
      (s n ^ m * (harmonic n : ℂ)⁻¹ ^ 2) *
        ((((m + 1).factorial : ℕ) : ℂ) *
          shiftedHarmonicPowerSum (m + 2) n (z n))) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hmajor : Tendsto (fun n : ℕ =>
        ((((m + 1).factorial : ℕ) : ℝ) * 2 ^ (m + 2)) *
          ‖s n ^ m * (harmonic n : ℂ)⁻¹ ^ 1‖) atTop (𝓝 0) := by
      simpa using
        ((tendsto_scale_pow_mul_inv_harmonic_pow m (by norm_num : 0 < 1)).norm.const_mul
          ((((m + 1).factorial : ℕ) : ℝ) * 2 ^ (m + 2)))
    apply squeeze_zero' (Filter.Eventually.of_forall fun n => norm_nonneg _) _ hmajor
    filter_upwards [hsmall, Filter.eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hzn hn
    have hHreal : 0 < (harmonic n : ℝ) := by
      exact_mod_cast harmonic_pos (by omega : n ≠ 0)
    have hbound := norm_shiftedHarmonicPowerSum_le hzn (p := m + 2) (by omega) n
    have hnormH : ‖(harmonic n : ℂ)‖ = (harmonic n : ℝ) := by
      rw [show (harmonic n : ℂ) = ((harmonic n : ℝ) : ℂ) by norm_cast]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hHreal]
    have hinvnorm : ‖(harmonic n : ℂ)⁻¹‖ = (harmonic n : ℝ)⁻¹ := by
      rw [norm_inv, hnormH]
    rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, hinvnorm]
    simp only [Complex.norm_natCast]
    calc
      ‖s n‖ ^ m * ((harmonic n : ℝ)⁻¹) ^ 2 *
          ((((m + 1).factorial : ℕ) : ℝ) *
            ‖shiftedHarmonicPowerSum (m + 2) n (z n)‖) ≤
        ‖s n‖ ^ m * ((harmonic n : ℝ)⁻¹) ^ 2 *
          ((((m + 1).factorial : ℕ) : ℝ) *
            (2 ^ (m + 2) * (harmonic n : ℝ))) := by gcongr
      _ = ((((m + 1).factorial : ℕ) : ℝ) * 2 ^ (m + 2)) *
            ‖s n ^ m * (harmonic n : ℂ)⁻¹ ^ 1‖ := by
        rw [norm_mul, norm_pow, norm_pow, hinvnorm]
        field_simp
  have hregular : ∀ᶠ n : ℕ in atTop, ∀ j : ℤ, z n ≠ (j : ℂ) := by
    have hlt : ∀ᶠ n : ℕ in atTop, ‖z n‖ < 1 :=
      hz.norm.eventually_lt_const (by norm_num)
    filter_upwards [hlt] with n hzn j
    have hsn : s n ≠ 0 := by
      dsimp [s]
      exact div_ne_zero (pow_ne_zero _ (by norm_num))
        (by exact_mod_cast Nat.factorial_ne_zero n)
    exact ne_intCast_of_ne_zero_of_norm_lt_one (mul_ne_zero hsn hx) hzn j
  have heq : ∀ᶠ n : ℕ in atTop,
      (gammaFactorialScaledPolygamma (m + 1) n x -
            (-1) ^ (m + 2) * (((m + 1).factorial : ℕ) : ℂ) * x⁻¹ ^ (m + 2)) /
          gammaHarmonicMicroscopeScale n ^ 2 =
        (s n ^ m * (harmonic n : ℂ)⁻¹ ^ 2) *
          (iteratedDeriv (m + 1) Complex.digamma (1 + z n) +
            (((m + 1).factorial : ℕ) : ℂ) *
              shiftedHarmonicPowerSum (m + 2) n (z n)) := by
    filter_upwards [hregular, Filter.eventually_atTop.2 ⟨1, fun n hn => hn⟩]
      with n hzn hn
    have hsn : s n ≠ 0 := by
      dsimp [s]
      exact div_ne_zero (pow_ne_zero _ (by norm_num))
        (by exact_mod_cast Nat.factorial_ne_zero n)
    have hH : (harmonic n : ℂ) ≠ 0 := by
      exact_mod_cast (harmonic_pos (by omega : n ≠ 0)).ne'
    have hformula := iteratedDeriv_digamma_neg_nat_add_of_ne_int (m + 1) (z n) hzn n
    have hcancel : s n ^ (m + 2) *
        ((-1) ^ (m + 2) * (((m + 1).factorial : ℕ) : ℂ) * (z n)⁻¹ ^ (m + 2)) =
        (-1) ^ (m + 2) * (((m + 1).factorial : ℕ) : ℂ) * x⁻¹ ^ (m + 2) := by
      have hpow := scale_pow_mul_inv_pow (s := s n) (x := x) hsn (m + 2)
      calc
        s n ^ (m + 2) *
            ((-1) ^ (m + 2) * (((m + 1).factorial : ℕ) : ℂ) * (z n)⁻¹ ^ (m + 2)) =
            (-1) ^ (m + 2) * (((m + 1).factorial : ℕ) : ℂ) *
              (s n ^ (m + 2) * (s n * x)⁻¹ ^ (m + 2)) := by
          dsimp only [z]
          ring
        _ = (-1) ^ (m + 2) * (((m + 1).factorial : ℕ) : ℂ) * x⁻¹ ^ (m + 2) := by
          rw [hpow]
    rw [gammaFactorialScaledPolygamma, gammaHarmonicMicroscopeScale]
    change (s n ^ (m + 1 + 1) *
        iteratedDeriv (m + 1) Complex.digamma (-(n : ℂ) + z n) -
        (-1) ^ (m + 2) * (((m + 1).factorial : ℕ) : ℂ) * x⁻¹ ^ (m + 2)) /
          (s n * (harmonic n : ℂ)) ^ 2 = _
    rw [hformula]
    have hnum : s n ^ (m + 1 + 1) *
          (iteratedDeriv (m + 1) Complex.digamma (1 + z n) +
              (-1) ^ (m + 1 + 1) * (((m + 1).factorial : ℕ) : ℂ) *
                (z n)⁻¹ ^ (m + 1 + 1) +
            (((m + 1).factorial : ℕ) : ℂ) *
              shiftedHarmonicPowerSum (m + 1 + 1) n (z n)) -
          (-1) ^ (m + 2) * (((m + 1).factorial : ℕ) : ℂ) * x⁻¹ ^ (m + 2) =
        s n ^ (m + 2) *
          (iteratedDeriv (m + 1) Complex.digamma (1 + z n) +
            (((m + 1).factorial : ℕ) : ℂ) *
              shiftedHarmonicPowerSum (m + 2) n (z n)) := by
      have h2 : m + 1 + 1 = m + 2 := rfl
      rw [h2]
      linear_combination hcancel
    rw [hnum, pow_add]
    field_simp
  have hcombined : Tendsto (fun n : ℕ =>
      (s n ^ m * (harmonic n : ℂ)⁻¹ ^ 2) *
        (iteratedDeriv (m + 1) Complex.digamma (1 + z n) +
          (((m + 1).factorial : ℕ) : ℂ) *
            shiftedHarmonicPowerSum (m + 2) n (z n))) atTop (𝓝 0) := by
    have h : Tendsto (fun n : ℕ =>
        (s n ^ m * (harmonic n : ℂ)⁻¹ ^ 2) *
            iteratedDeriv (m + 1) Complex.digamma (1 + z n) +
          (s n ^ m * (harmonic n : ℂ)⁻¹ ^ 2) *
            ((((m + 1).factorial : ℕ) : ℂ) *
              shiftedHarmonicPowerSum (m + 2) n (z n))) atTop (𝓝 0) := by
      simpa using hlocal.add hsum
    exact h.congr fun n => by ring
  exact hcombined.congr' (heq.mono fun _ h => h.symm)

/-- The scaled trigamma has no correction at quadratic harmonic order. -/
theorem tendsto_gammaFactorialScaledTrigamma_second_harmonic
    {x : ℂ} (hx : x ≠ 0) :
    Tendsto (fun n : ℕ =>
      (gammaFactorialScaledTrigamma n x - x⁻¹ ^ 2) /
        gammaHarmonicMicroscopeScale n ^ 2) atTop (𝓝 0) := by
  have h := tendsto_gammaFactorialScaledPolygamma_second_harmonic 0 hx
  simpa [gammaFactorialScaledTrigamma_eq_polygamma] using h

/-- The scaled order-two polygamma has no correction at quadratic harmonic order. -/
theorem tendsto_gammaFactorialScaledSecondPolygamma_second_harmonic
    {x : ℂ} (hx : x ≠ 0) :
    Tendsto (fun n : ℕ =>
      (gammaFactorialScaledSecondPolygamma n x - 2 * (-x)⁻¹ ^ 3) /
        gammaHarmonicMicroscopeScale n ^ 2) atTop (𝓝 0) := by
  have h := tendsto_gammaFactorialScaledPolygamma_second_harmonic 1 hx
  refine h.congr fun n => ?_
  rw [gammaFactorialScaledSecondPolygamma_eq_polygamma, inv_neg]
  norm_num
  ring

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
