import GaloisForLFunctions.HTGeometry.GammaFactorialMovingHarmonicResidue

/-!
# Moving second-jet harmonic residue of the Gamma factorial microscope

At the reciprocal boundary `M=-1/x`, the second-jet equation is `M''=2M³`.  This file proves that
the exact Gamma zoom crosses that equation at the first harmonic scale:

`(gₙ''-2gₙ³)/(sₙHₙ) → 6/x²`.

The proof establishes the needed scaled-trigamma correction directly from the finite polygamma
shift law and a uniform shifted-square harmonic bound.  No numerical approximation is used.
-/

namespace GaloisForLFunctions

open Complex Filter Topology

noncomputable section

def shiftedHarmonicSquareSum (n : ℕ) (z : ℂ) : ℂ :=
  ∑ j ∈ Finset.range n, ((((j + 1 : ℕ) : ℂ) - z) ^ 2)⁻¹

theorem iteratedDeriv_one_digamma_neg_nat_add_of_ne_int (z : ℂ)
    (hz : ∀ k : ℤ, z ≠ (k : ℂ)) (n : ℕ) :
    iteratedDeriv 1 Complex.digamma (-(n : ℂ) + z) =
      iteratedDeriv 1 Complex.digamma (1 + z) + z⁻¹ ^ 2 +
        shiftedHarmonicSquareSum n z := by
  induction n with
  | zero =>
      have hzOff : ∀ k : ℕ, z ≠ -(k : ℂ) := by
        intro k
        simpa using hz (-(k : ℤ))
      have hstep := digammaJet_shift 1 hzOff
      simp only [Nat.cast_zero, neg_zero, zero_add, shiftedHarmonicSquareSum,
        Finset.range_zero, Finset.sum_empty, add_zero]
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
      have hstep := digammaJet_shift 1 hw
      have hwadd : w + 1 = -(n : ℂ) + z := by
        dsimp [w]
        push_cast
        ring
      have hwpow : w ^ 2 = (((n + 1 : ℕ) : ℂ) - z) ^ 2 := by
        dsimp [w]
        ring
      change iteratedDeriv 1 Complex.digamma w = _
      have hsolve : iteratedDeriv 1 Complex.digamma w =
          iteratedDeriv 1 Complex.digamma (w + 1) + (w ^ 2)⁻¹ := by
        simp only [iteratedDeriv_one] at hstep ⊢
        rw [hstep]
        norm_num
        ring
      rw [hsolve, hwadd, ih]
      simp only [shiftedHarmonicSquareSum, Finset.sum_range_succ, hwpow]
      ring

theorem norm_shiftedInverse_le {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) (j : ℕ) :
    ‖(((j + 1 : ℕ) : ℂ) - z)⁻¹‖ ≤ 2 / ((j + 1 : ℕ) : ℝ) := by
  let k : ℝ := ((j + 1 : ℕ) : ℝ)
  have hk : 1 ≤ k := by
    dsimp [k]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le j)
  have hkpos : 0 < k := lt_of_lt_of_le zero_lt_one hk
  have hnormk : ‖((j + 1 : ℕ) : ℂ)‖ = k := by
    rw [Complex.norm_natCast]
  have hrev := norm_sub_norm_le ((j + 1 : ℕ) : ℂ) z
  rw [hnormk] at hrev
  have hhalf : k / 2 ≤ ‖((j + 1 : ℕ) : ℂ) - z‖ := by
    nlinarith
  have hden : 0 < ‖((j + 1 : ℕ) : ℂ) - z‖ :=
    lt_of_lt_of_le (half_pos hkpos) hhalf
  rw [norm_inv]
  change ‖((j + 1 : ℕ) : ℂ) - z‖⁻¹ ≤ 2 / k
  calc
    ‖((j + 1 : ℕ) : ℂ) - z‖⁻¹ ≤ (k / 2)⁻¹ :=
      (inv_le_inv₀ hden (half_pos hkpos)).2 hhalf
    _ = 2 / k := by field_simp

theorem norm_shiftedHarmonicSquareSum_le {z : ℂ}
    (hz : ‖z‖ ≤ 1 / 2) (n : ℕ) :
    ‖shiftedHarmonicSquareSum n z‖ ≤ 4 * (harmonic n : ℝ) := by
  rw [shiftedHarmonicSquareSum]
  calc
    ‖∑ j ∈ Finset.range n, ((((j + 1 : ℕ) : ℂ) - z) ^ 2)⁻¹‖ ≤
        ∑ j ∈ Finset.range n, ‖((((j + 1 : ℕ) : ℂ) - z) ^ 2)⁻¹‖ :=
      norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range n, 4 / ((j + 1 : ℕ) : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [← inv_pow, norm_pow]
      have h := norm_shiftedInverse_le hz j
      have hk : 1 ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le j)
      have hnon : 0 ≤ ‖(((j + 1 : ℕ) : ℂ) - z)⁻¹‖ := norm_nonneg _
      calc
        ‖(↑(j + 1) - z)⁻¹‖ ^ 2 ≤ (2 / ((j + 1 : ℕ) : ℝ)) ^ 2 :=
          (sq_le_sq₀ hnon (by positivity)).2 h
        _ ≤ 4 / ((j + 1 : ℕ) : ℝ) := by
          have hkpos : 0 < ((j + 1 : ℕ) : ℝ) := lt_of_lt_of_le zero_lt_one hk
          field_simp [hkpos.ne']
          nlinarith
    _ = 4 * (harmonic n : ℝ) := by
      rw [harmonic]
      push_cast
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      field_simp

def gammaFactorialScaledTrigamma (n : ℕ) (x : ℂ) : ℂ :=
  reciprocalGammaFactorialScale n ^ 2 *
    iteratedDeriv 1 Complex.digamma
      (-(n : ℂ) + reciprocalGammaFactorialScale n * x)

theorem tendsto_gammaFactorialScaledTrigamma_first_harmonic
    {x : ℂ} (hx : x ≠ 0) :
    Tendsto (fun n : ℕ =>
      (gammaFactorialScaledTrigamma n x - x⁻¹ ^ 2) /
        gammaHarmonicMicroscopeScale n) atTop (𝓝 0) := by
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
  have hpsi : Tendsto (fun n => iteratedDeriv 1 Complex.digamma (1 + z n))
      atTop (𝓝 (iteratedDeriv 1 Complex.digamma 1)) :=
    (analyticAt_iteratedDeriv_of_analyticAt (analyticAt_digamma_of_offPoles hOff1) 1).continuousAt.tendsto.comp
      hinput
  have hsdivH : Tendsto (fun n => s n * (harmonic n : ℂ)⁻¹)
      atTop (𝓝 0) := by
    simpa using hs.mul tendsto_inv_harmonic_cast_complex_zero
  have hlocal : Tendsto (fun n =>
      (s n * (harmonic n : ℂ)⁻¹) *
        iteratedDeriv 1 Complex.digamma (1 + z n)) atTop (𝓝 0) := by
    simpa using hsdivH.mul hpsi
  have hsmall : ∀ᶠ n : ℕ in atTop, ‖z n‖ ≤ 1 / 2 :=
    (hz.norm.eventually_lt_const (by norm_num)).mono fun _ h => h.le
  have hsum : Tendsto (fun n =>
      (s n * (harmonic n : ℂ)⁻¹) * shiftedHarmonicSquareSum n (z n))
      atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hmajor : Tendsto (fun n => 4 * ‖s n‖) atTop (𝓝 0) := by
      simpa using hs.norm.const_mul 4
    apply squeeze_zero' (Filter.Eventually.of_forall fun n => norm_nonneg _) _ hmajor
    filter_upwards [hsmall, Filter.eventually_atTop.2 ⟨1, fun n hn => hn⟩]
      with n hzn hn
    have hHreal : 0 < (harmonic n : ℝ) := by
      exact_mod_cast harmonic_pos (by omega : n ≠ 0)
    have hH : (harmonic n : ℂ) ≠ 0 := by exact_mod_cast hHreal.ne'
    have hbound := norm_shiftedHarmonicSquareSum_le hzn n
    rw [norm_mul, norm_mul, norm_inv]
    have hnormH : ‖(harmonic n : ℂ)‖ = (harmonic n : ℝ) := by
      rw [show (harmonic n : ℂ) = ((harmonic n : ℝ) : ℂ) by norm_cast]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hHreal]
    rw [hnormH]
    calc
      ‖s n‖ * (harmonic n : ℝ)⁻¹ * ‖shiftedHarmonicSquareSum n (z n)‖ ≤
          ‖s n‖ * (harmonic n : ℝ)⁻¹ * (4 * (harmonic n : ℝ)) := by
            gcongr
      _ = 4 * ‖s n‖ := by field_simp [hHreal.ne']
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
          gammaHarmonicMicroscopeScale n =
        (s n * (harmonic n : ℂ)⁻¹) *
            iteratedDeriv 1 Complex.digamma (1 + z n) +
          (s n * (harmonic n : ℂ)⁻¹) * shiftedHarmonicSquareSum n (z n) := by
    filter_upwards [hregular, Filter.eventually_atTop.2 ⟨1, fun n hn => hn⟩]
      with n hzn hn
    have hsn : s n ≠ 0 := by
      dsimp [s]
      exact div_ne_zero (pow_ne_zero _ (by norm_num))
        (by exact_mod_cast Nat.factorial_ne_zero n)
    have hH : (harmonic n : ℂ) ≠ 0 := by
      exact_mod_cast (harmonic_pos (by omega : n ≠ 0)).ne'
    have hformula := iteratedDeriv_one_digamma_neg_nat_add_of_ne_int
      (z n) hzn n
    rw [gammaFactorialScaledTrigamma, gammaHarmonicMicroscopeScale]
    change (s n ^ 2 * iteratedDeriv 1 Complex.digamma (-↑n + z n) - x⁻¹ ^ 2) /
      (s n * (harmonic n : ℂ)) = _
    rw [hformula]
    dsimp [z]
    field_simp [hsn, hH, hx]
    ring
  simpa using hlimit.congr' (heq.mono fun _ h => h.symm)

theorem tendsto_gammaFactorialZoom_first_harmonic {x : ℂ} (hx : x ≠ 0) :
    Tendsto (fun n : ℕ =>
      (factorialBlowUpZoom Complex.Gamma n x - (-x)⁻¹) /
        gammaHarmonicMicroscopeScale n) atTop (𝓝 (-1)) := by
  have hh : Tendsto (fun n : ℕ =>
      reciprocalGammaEntire
        (-(n : ℂ) + reciprocalGammaFactorialScale n * x))
      atTop (𝓝 (-x)) :=
    tendsto_reciprocalGammaFactorialBlowUp_locallyUniformly.tendstoLocallyUniformlyOn.tendsto_at
      (Set.mem_univ x)
  have hhcor := tendsto_reciprocalGammaFactorialBlowUp_first_harmonic x
  have hden := hh.mul_const x
  have hquot := hhcor.div hden (mul_ne_zero (neg_ne_zero.mpr hx) hx)
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
  have hscale : ∀ᶠ n : ℕ in atTop, gammaHarmonicMicroscopeScale n ≠ 0 := by
    filter_upwards [Filter.eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
    exact gammaHarmonicMicroscopeScale_ne_zero hn
  have heq : ∀ᶠ n : ℕ in atTop,
      (factorialBlowUpZoom Complex.Gamma n x - (-x)⁻¹) /
          gammaHarmonicMicroscopeScale n =
        ((reciprocalGammaEntire
              (-(n : ℂ) + reciprocalGammaFactorialScale n * x) + x) /
            gammaHarmonicMicroscopeScale n) /
          (reciprocalGammaEntire
              (-(n : ℂ) + reciprocalGammaFactorialScale n * x) * x) := by
    filter_upwards [hregular, hscale] with n hn hs
    have hGamma := Complex.Gamma_ne_zero hn
    rw [factorialBlowUpZoom, reciprocalGammaEntire]
    field_simp [hGamma, hx, hs]
    ring
  have hfinal := hquot.congr' (heq.mono fun _ h => h.symm)
  have hlimval : x ^ 2 / (-x * x) = (-1 : ℂ) := by
    field_simp [hx]
  rw [hlimval] at hfinal
  exact hfinal

def gammaFactorialSecondJetDefect (n : ℕ) (x : ℂ) : ℂ :=
  iteratedDeriv 2 (factorialBlowUpZoom Complex.Gamma n) x -
    2 * factorialBlowUpZoom Complex.Gamma n x ^ 3

theorem gammaFactorialSecondJetDefect_eq
    (n : ℕ) (x : ℂ)
    (hpole : ∀ k : ℕ,
      -(n : ℂ) + reciprocalGammaFactorialScale n * x ≠ -(k : ℂ)) :
    gammaFactorialSecondJetDefect n x =
      factorialBlowUpZoom Complex.Gamma n x *
        (gammaFactorialScaledTrigamma n x +
          gammaFactorialScaledDigamma n x ^ 2 -
          2 * factorialBlowUpZoom Complex.Gamma n x ^ 2) := by
  let w : ℂ := -(n : ℂ) + reciprocalGammaFactorialScale n * x
  have hBell := iteratedDeriv_two_Gamma_eq_logDeriv w hpole
  have hpsi : (fun z => deriv Complex.Gamma z / Complex.Gamma z) =
      Complex.digamma := by
    funext z
    rw [Complex.digamma_def, logDeriv_apply]
  rw [gammaFactorialSecondJetDefect, iteratedDeriv_factorialBlowUpZoom]
  rw [show iteratedDeriv 2 Complex.Gamma w = _ from hBell]
  rw [hpsi]
  simp only [factorialBlowUpZoom, gammaFactorialScaledTrigamma,
    gammaFactorialScaledDigamma]
  simp only [iteratedDeriv_one]
  have hratio : deriv Complex.Gamma w / Complex.Gamma w = Complex.digamma w := by
    rw [Complex.digamma_def, logDeriv_apply]
  dsimp only [w] at hratio
  rw [hratio]
  ring

theorem tendsto_gammaFactorialSecondJetDefect_div_harmonicScale
    {x : ℂ} (hx : x ≠ 0) :
    Tendsto (fun n : ℕ =>
      gammaFactorialSecondJetDefect n x / gammaHarmonicMicroscopeScale n)
      atTop (𝓝 (6 / x ^ 2)) := by
  let g : ℕ → ℂ := fun n => factorialBlowUpZoom Complex.Gamma n x
  let q : ℕ → ℂ := fun n => gammaFactorialScaledDigamma n x
  let T : ℕ → ℂ := fun n => gammaFactorialScaledTrigamma n x
  let M : ℂ := (-x)⁻¹
  let a : ℕ → ℂ := gammaHarmonicMicroscopeScale
  have ha0 : Tendsto a atTop (𝓝 0) := tendsto_gammaHarmonicMicroscopeScale_zero
  have hane : ∀ᶠ n : ℕ in atTop, a n ≠ 0 := by
    filter_upwards [Filter.eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
    exact gammaHarmonicMicroscopeScale_ne_zero hn
  have hgcor : Tendsto (fun n => (g n - M) / a n) atTop (𝓝 (-1)) := by
    simpa [g, M, a] using tendsto_gammaFactorialZoom_first_harmonic hx
  have hqcor : Tendsto (fun n => (q n - M) / a n) atTop (𝓝 1) := by
    simpa [q, M, a, sub_eq_add_neg] using
      tendsto_gammaFactorialScaledDigamma_first_harmonic hx
  have hTcor : Tendsto (fun n => (T n - M ^ 2) / a n) atTop (𝓝 0) := by
    simpa [T, M, a] using tendsto_gammaFactorialScaledTrigamma_first_harmonic hx
  have hgdiff : Tendsto (fun n => g n - M) atTop (𝓝 0) := by
    have h := hgcor.mul ha0
    have heq : ∀ᶠ n in atTop, (g n - M) / a n * a n = g n - M := by
      filter_upwards [hane] with n hn
      field_simp [hn]
    simpa using h.congr' heq
  have hqdiff : Tendsto (fun n => q n - M) atTop (𝓝 0) := by
    have h := hqcor.mul ha0
    have heq : ∀ᶠ n in atTop, (q n - M) / a n * a n = q n - M := by
      filter_upwards [hane] with n hn
      field_simp [hn]
    simpa using h.congr' heq
  have hTdiff : Tendsto (fun n => T n - M ^ 2) atTop (𝓝 0) := by
    have h := hTcor.mul ha0
    have heq : ∀ᶠ n in atTop, (T n - M ^ 2) / a n * a n = T n - M ^ 2 := by
      filter_upwards [hane] with n hn
      field_simp [hn]
    simpa using h.congr' heq
  have hg : Tendsto g atTop (𝓝 M) := by
    have h := hgdiff.add_const M
    simpa [sub_add_cancel] using h
  have hq : Tendsto q atTop (𝓝 M) := by
    have h := hqdiff.add_const M
    simpa [sub_add_cancel] using h
  have hT : Tendsto T atTop (𝓝 (M ^ 2)) := by
    have h := hTdiff.add_const (M ^ 2)
    simpa [sub_add_cancel] using h
  have hqsum : Tendsto (fun n => q n + M) atTop (𝓝 (2 * M)) := by
    simpa [two_mul] using hq.add_const M
  have hgsum : Tendsto (fun n => g n + M) atTop (𝓝 (2 * M)) := by
    simpa [two_mul] using hg.add_const M
  have hqSq : Tendsto (fun n => (q n ^ 2 - M ^ 2) / a n)
      atTop (𝓝 (2 * M)) := by
    have h := hqcor.mul hqsum
    have heq : ∀ᶠ n in atTop,
        (q n - M) / a n * (q n + M) = (q n ^ 2 - M ^ 2) / a n := by
      filter_upwards [hane] with n hn
      field_simp [hn]
      ring
    simpa using h.congr' heq
  have hgSq : Tendsto (fun n => (g n ^ 2 - M ^ 2) / a n)
      atTop (𝓝 (-2 * M)) := by
    have h := hgcor.mul hgsum
    have heq : ∀ᶠ n in atTop,
        (g n - M) / a n * (g n + M) = (g n ^ 2 - M ^ 2) / a n := by
      filter_upwards [hane] with n hn
      field_simp [hn]
      ring
    simpa using h.congr' heq
  have hbracket : Tendsto (fun n =>
      (T n + q n ^ 2 - 2 * g n ^ 2) / a n) atTop (𝓝 (6 * M)) := by
    have h := (hTcor.add hqSq).sub (hgSq.const_mul 2)
    convert h using 1
    · funext n
      by_cases hn : a n = 0
      · simp [hn]
      · field_simp [hn]
        ring
    · ring_nf
  have hproduct := hg.mul hbracket
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
      gammaFactorialSecondJetDefect n x / gammaHarmonicMicroscopeScale n =
        g n * ((T n + q n ^ 2 - 2 * g n ^ 2) / a n) := by
    filter_upwards [hregular] with n hn
    rw [gammaFactorialSecondJetDefect_eq n x hn]
    simp only [g, q, T, a]
    ring
  have hfinal := hproduct.congr' (heq.mono fun _ h => h.symm)
  have hlimval : M * (6 * M) = 6 / x ^ 2 := by
    dsimp [M]
    field_simp [hx]
  rw [hlimval] at hfinal
  exact hfinal

/-- The derivative-weight-homogeneous projective curvature of the Gamma zoom.  It vanishes on the
reciprocal boundary even though neither monomial is removed by derivative grading. -/
def gammaFactorialSecondJetProjectiveDefect (n : ℕ) (x : ℂ) : ℂ :=
  factorialBlowUpZoom Complex.Gamma n x *
      iteratedDeriv 2 (factorialBlowUpZoom Complex.Gamma n) x -
    2 * iteratedDeriv 1 (factorialBlowUpZoom Complex.Gamma n) x ^ 2

theorem gammaFactorialSecondJetProjectiveDefect_eq
    (n : ℕ) (x : ℂ) :
    gammaFactorialSecondJetProjectiveDefect n x =
      factorialBlowUpZoom Complex.Gamma n x * gammaFactorialSecondJetDefect n x -
        4 * factorialBlowUpZoom Complex.Gamma n x ^ 2 *
          gammaFactorialFirstJetDefect n x -
        2 * gammaFactorialFirstJetDefect n x ^ 2 := by
  rw [gammaFactorialSecondJetProjectiveDefect, gammaFactorialSecondJetDefect,
    gammaFactorialFirstJetDefect]
  ring

/-- **First genuinely homogeneous projective residue.**  The reciprocal second-jet curvature
`g g''-2(g')²` is invisible to derivative grading, but the exact Gamma zoom crosses it at the first
harmonic scale with nonzero limit `2/x³`. -/
theorem tendsto_gammaFactorialSecondJetProjectiveDefect_div_harmonicScale
    {x : ℂ} (hx : x ≠ 0) :
    Tendsto (fun n : ℕ =>
      gammaFactorialSecondJetProjectiveDefect n x /
        gammaHarmonicMicroscopeScale n) atTop (𝓝 (2 / x ^ 3)) := by
  let g : ℕ → ℂ := fun n => factorialBlowUpZoom Complex.Gamma n x
  let R : ℕ → ℂ := fun n => gammaFactorialFirstJetDefect n x
  let C : ℕ → ℂ := fun n => gammaFactorialSecondJetDefect n x
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
  have hRcor : Tendsto (fun n => R n / a n) atTop (𝓝 (2 * M)) := by
    have h := tendsto_gammaFactorialFirstJetDefect_div_harmonicScale hx
    have hval : -2 / x = 2 * M := by
      dsimp [M]
      field_simp [hx]
    rw [hval] at h
    simpa [R, a] using h
  have hR : Tendsto R atTop (𝓝 0) := by
    have h := hRcor.mul ha0
    have heq : ∀ᶠ n in atTop, R n / a n * a n = R n := by
      filter_upwards [hane] with n hn
      field_simp [hn]
    simpa using h.congr' heq
  have hCcor : Tendsto (fun n => C n / a n) atTop (𝓝 (6 * M ^ 2)) := by
    have h := tendsto_gammaFactorialSecondJetDefect_div_harmonicScale hx
    have hval : 6 / x ^ 2 = 6 * M ^ 2 := by
      dsimp [M]
      field_simp [hx]
    rw [hval] at h
    simpa [C, a] using h
  have hlimit := (hg.mul hCcor).sub
    ((hg.pow 2).mul hRcor |>.const_mul 4) |>.sub (hRcor.mul hR |>.const_mul 2)
  have heq : ∀ᶠ n : ℕ in atTop,
      gammaFactorialSecondJetProjectiveDefect n x / a n =
        g n * (C n / a n) - 4 * (g n ^ 2 * (R n / a n)) -
          2 * ((R n / a n) * R n) := by
    filter_upwards [hane] with n hn
    rw [gammaFactorialSecondJetProjectiveDefect_eq]
    simp only [g, R, C]
    field_simp [hn]
  have hfinal := hlimit.congr' (heq.mono fun _ h => h.symm)
  have hlimval : M * (6 * M ^ 2) - 4 * (M ^ 2 * (2 * M)) -
      2 * (2 * M * 0) = 2 / x ^ 3 := by
    dsimp [M]
    field_simp [hx]
    ring
  rw [hlimval] at hfinal
  simpa [a] using hfinal

end

end GaloisForLFunctions
