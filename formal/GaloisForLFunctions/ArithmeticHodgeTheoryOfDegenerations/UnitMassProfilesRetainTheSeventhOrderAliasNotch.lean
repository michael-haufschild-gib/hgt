import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheAliasNotchOrderIsSetByTheSpectralTail
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheAliasingIsTheDilationDerivativeOfTheBulk
import GaloisForLFunctions.SquareRootThreshold.EveryWidthDecidesTheCriticalLine
import GaloisForLFunctions.RHTower.WeilMarkovPrimitiveHyperplane

/-!
# Unit-mass profiles with high-order harmonic zeros

An even cardinal spline and an odd centered difference have orthogonal Fourier
transforms on the real axis. Adding them restores integral one while retaining
the seventh-order aliasing notch of the difference term.
-/

noncomputable section
set_option autoImplicit false

open MeasureTheory Set Filter Topology Complex
open scoped ComplexConjugate

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.SplineAliasNotches

open Zeta23 RenormalizedArithmeticPotentialTheory.CompletedShell
open BiScaleUncertainty.ChebyshevGauge
open RHTower.WeilDeletion (upow unif paperFT_upow integral_upow
  hasCompactSupport_upow support_upow_subset)

/-- The centered cardinal spline with `n+4` box factors. -/
def cardinalSpline (n : ℕ) : ℝ → ℝ := upow (1 / 2) (n + 3)

/-- Centering an integer difference changes only its Fourier phase. -/
def centeredDifferenceSpline (n : ℕ) (u : ℝ) : ℝ := differenceSpline n (u + n / 2)

/-- An even spline plus an odd difference, with integral one. -/
def unitNotchProfile (r : ℕ) (u : ℝ) : ℝ :=
  cardinalSpline (2 * r + 1) u + centeredDifferenceSpline (2 * r + 1) u

theorem contDiff_cardinalSpline (n : ℕ) : ContDiff ℝ 2 (cardinalSpline n) := by
  have h := contDiff_upow (by norm_num : (0 : ℝ) < 1 / 2) (n + 2)
  exact h.of_le (by exact_mod_cast (show 2 ≤ n + 2 by omega))

theorem cardinalSpline_support (n : ℕ) {u : ℝ} (hu : cardinalSpline n u ≠ 0) :
    |u| ≤ 2 * (n : ℝ) + 2 := by
  have h := support_upow_subset (by norm_num : (0 : ℝ) < 1 / 2) (n + 3) hu
  have ha := abs_le.mpr h
  push_cast at ha
  have hn := Nat.cast_nonneg (α := ℝ) n
  linarith only [ha, hn]

theorem hasCompactSupport_cardinalSpline (n : ℕ) : HasCompactSupport (cardinalSpline n) :=
  hasCompactSupport_upow _ _

theorem integral_cardinalSpline (n : ℕ) : ∫ u, cardinalSpline n u = 1 :=
  integral_upow (by norm_num) _

theorem contDiff_centeredDifferenceSpline (n : ℕ) :
    ContDiff ℝ 2 (centeredDifferenceSpline n) :=
  (contDiff_differenceSpline n).comp (contDiff_id.add contDiff_const)

theorem centeredDifferenceSpline_support (n : ℕ) {u : ℝ}
    (hu : centeredDifferenceSpline n u ≠ 0) : |u| ≤ 2 * (n : ℝ) + 2 := by
  have h := differenceSpline_support n hu
  have he : u + (n : ℝ) / 2 + -((n : ℝ) / 2) = u := by ring
  have ht : |u| ≤ |u + (n : ℝ) / 2| + (n : ℝ) / 2 := by
    simpa only [he, abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ n / 2)]
      using abs_add_le (u + (n : ℝ) / 2) (-((n : ℝ) / 2))
  have hn := Nat.cast_nonneg (α := ℝ) n
  linarith only [h, ht, hn]

theorem hasCompactSupport_centeredDifferenceSpline (n : ℕ) :
    HasCompactSupport (centeredDifferenceSpline n) :=
  hasCompactSupport_of_support_subset_abs fun _ hu => centeredDifferenceSpline_support n hu

theorem integral_centeredDifferenceSpline_succ (n : ℕ) :
    ∫ u, centeredDifferenceSpline (n + 1) u = 0 := by
  simp only [centeredDifferenceSpline]
  rw [integral_add_right_eq_self, integral_differenceSpline_succ]

theorem contDiff_unitNotchProfile (r : ℕ) : ContDiff ℝ 2 (unitNotchProfile r) :=
  (contDiff_cardinalSpline _).add (contDiff_centeredDifferenceSpline _)

theorem hasCompactSupport_unitNotchProfile (r : ℕ) : HasCompactSupport (unitNotchProfile r) :=
  (hasCompactSupport_cardinalSpline _).add (hasCompactSupport_centeredDifferenceSpline _)

theorem integral_unitNotchProfile (r : ℕ) : ∫ u, unitNotchProfile r u = 1 := by
  have hc₁ := (contDiff_cardinalSpline (2 * r + 1)).continuous
  have hc₂ := (contDiff_centeredDifferenceSpline (2 * r + 1)).continuous
  have hi₁ : Integrable (cardinalSpline (2 * r + 1)) :=
    hc₁.integrable_of_hasCompactSupport (hasCompactSupport_cardinalSpline _)
  have hi₂ : Integrable (centeredDifferenceSpline (2 * r + 1)) :=
    hc₂.integrable_of_hasCompactSupport (hasCompactSupport_centeredDifferenceSpline _)
  simp only [unitNotchProfile]
  rw [integral_add hi₁ hi₂, integral_cardinalSpline,
    integral_centeredDifferenceSpline_succ, add_zero]

theorem differenceSpline_reflect (n : ℕ) (u : ℝ) :
    differenceSpline n ((n : ℝ) - u) = (-1 : ℝ) ^ n * differenceSpline n u := by
  induction n generalizing u with
  | zero =>
      simpa only [differenceSpline, Nat.cast_zero, zero_sub, pow_zero, one_mul] using
        SquareRootThreshold.upow_neg (1 / 2) 3 u
  | succ n ih =>
      have h₁ : ((n + 1 : ℕ) : ℝ) - u = (n : ℝ) - (u - 1) := by push_cast; ring
      have h₂ : ((n + 1 : ℕ) : ℝ) - u - 1 = (n : ℝ) - u := by push_cast; ring
      simp only [differenceSpline]
      rw [h₂, h₁, ih, ih, pow_succ]
      ring

theorem centeredDifferenceSpline_neg (n : ℕ) (u : ℝ) :
    centeredDifferenceSpline n (-u) = (-1 : ℝ) ^ n * centeredDifferenceSpline n u := by
  have he : (n : ℝ) - (u + (n : ℝ) / 2) = -u + (n : ℝ) / 2 := by ring
  simpa only [centeredDifferenceSpline, he] using differenceSpline_reflect n (u + n / 2)

theorem centeredDifferenceSpline_odd (r : ℕ) (u : ℝ) :
    centeredDifferenceSpline (2 * r + 1) (-u) = -centeredDifferenceSpline (2 * r + 1) u := by
  rw [centeredDifferenceSpline_neg]
  have he : (-1 : ℝ) ^ (2 * r + 1) = -1 := by rw [pow_add, pow_mul]; norm_num
  rw [he, neg_one_mul]

theorem shellSpectrum_centeredDifferenceSpline (n : ℕ) (t : ℝ) :
    shellSpectrum (centeredDifferenceSpline n) t = shellSpectrum (differenceSpline n) t := by
  have he : (fun u => (centeredDifferenceSpline n u : ℂ)) =
      fun u => (differenceSpline n (u - (-(n : ℝ) / 2)) : ℂ) := by
    funext u
    simp only [centeredDifferenceSpline, neg_div, sub_neg_eq_add]
  unfold shellSpectrum
  rw [he, RHTower.WeilDeletion.paperFT_translate, norm_mul, Complex.norm_exp]
  have hre : (I * ((2 * Real.pi * t : ℝ) : ℂ) * ((-(n : ℝ) / 2 : ℝ) : ℂ)).re = 0 := by
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [hre, Real.exp_zero, one_mul]

private theorem summable_alias_harmonics {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) {s : ℝ} (hs : 0 < s) :
    Summable (fun k : ℕ => shellSpectrum f (((k : ℝ) + 1) * s)) := by
  obtain ⟨C, -, hC⟩ := exists_shellSpectrum_le hf hfc
  exact Summable.of_nonneg_of_le (fun _ => shellSpectrum_nonneg _)
    (fun k => shellSpectrum_succ_mul_le hC hs le_rfl k)
    (summable_inv_succ_pow_four.mul_left (C ^ 2 / (2 * Real.pi * s) ^ 4))

/-- Even and odd components contribute separate nonnegative squared spectra. -/
theorem shellSpectrum_unitNotchProfile (r : ℕ) (t : ℝ) :
    shellSpectrum (unitNotchProfile r) t =
      shellSpectrum (cardinalSpline (2 * r + 1)) t +
        shellSpectrum (differenceSpline (2 * r + 1)) t := by
  let b := cardinalSpline (2 * r + 1)
  let g := centeredDifferenceSpline (2 * r + 1)
  have hb : Continuous b := (contDiff_cardinalSpline _).continuous
  have hg : Continuous g := (contDiff_centeredDifferenceSpline _).continuous
  have hbc : HasCompactSupport b := hasCompactSupport_cardinalSpline _
  have hgc : HasCompactSupport g := hasCompactSupport_centeredDifferenceSpline _
  have hFT : paperFT (fun u => (unitNotchProfile r u : ℂ)) ((2 * Real.pi * t : ℝ) : ℂ) =
      paperFT (fun u => (b u : ℂ)) ((2 * Real.pi * t : ℝ) : ℂ) +
        paperFT (fun u => (g u : ℂ)) ((2 * Real.pi * t : ℝ) : ℂ) := by
    have hi : ∀ (f : ℝ → ℝ), Continuous f → HasCompactSupport f →
        Integrable (fun u : ℝ => (f u : ℂ) * Complex.exp (I * ((2 * Real.pi * t : ℝ) : ℂ) * u)) := by
      intro f hf hfc
      have hc : Continuous (fun u : ℝ => (f u : ℂ) *
          Complex.exp (I * ((2 * Real.pi * t : ℝ) : ℂ) * u)) :=
        (Complex.continuous_ofReal.comp hf).mul (by fun_prop)
      exact hc.integrable_of_hasCompactSupport (hfc.comp_left Complex.ofReal_zero).mul_right
    simp only [paperFT, unitNotchProfile, Complex.ofReal_add, add_mul]
    exact integral_add (hi b hb hbc) (hi g hg hgc)
  have heven : ∀ u, b (-u) = b u := SquareRootThreshold.upow_neg _ _
  have hodd : ∀ u, g (-u) = -g u := centeredDifferenceSpline_odd r
  have hnorm := RHTower.normSq_add_of_conj_eq_of_conj_eq_neg
    (RHTower.paperFT_ofReal_conj_of_even heven (2 * Real.pi * t))
    (RHTower.paperFT_ofReal_conj_of_odd hodd (2 * Real.pi * t))
  simp only [Complex.normSq_eq_norm_sq] at hnorm
  calc
    shellSpectrum (unitNotchProfile r) t = shellSpectrum b t + shellSpectrum g t := by
      unfold shellSpectrum
      rw [hFT]
      exact hnorm
    _ = _ := by rw [show g = centeredDifferenceSpline (2 * r + 1) from rfl,
      shellSpectrum_centeredDifferenceSpline]

theorem aliasDensity_unitNotchProfile (r : ℕ) {s : ℝ} (hs : 0 < s) :
    aliasDensity (unitNotchProfile r) s =
      aliasDensity (cardinalSpline (2 * r + 1)) s +
        aliasDensity (differenceSpline (2 * r + 1)) s := by
  unfold aliasDensity
  simp_rw [shellSpectrum_unitNotchProfile]
  exact Summable.tsum_add
    (summable_alias_harmonics (contDiff_cardinalSpline _) (hasCompactSupport_cardinalSpline _) hs)
    (summable_alias_harmonics (contDiff_differenceSpline _) (hasCompactSupport_differenceSpline _) hs)

private theorem shellSpectrum_upow (n : ℕ) (t : ℝ) :
    shellSpectrum (upow (1 / 2) n) t = shellSpectrum (unif (1 / 2)) t ^ (n + 1) := by
  unfold shellSpectrum
  rw [paperFT_upow, norm_pow]
  simp only [← pow_mul]
  rw [Nat.mul_comm (n + 1) 2]

theorem weighted_cardinalSpectrum_add_int (n : ℕ) (j : ℤ) (x : ℝ) :
    ((j : ℝ) + x) ^ (2 * (n + 4)) * shellSpectrum (cardinalSpline n) ((j : ℝ) + x) =
      x ^ (2 * (n + 4)) * shellSpectrum (cardinalSpline n) x := by
  have hp := weighted_spectrum_add_int 0 j x
  simp only [differenceSpline, shellSpectrum_upow, Nat.reduceAdd] at hp
  have hfour : (((j : ℝ) + x) ^ 2 * shellSpectrum (unif (1 / 2)) ((j : ℝ) + x)) ^ 4 =
      (x ^ 2 * shellSpectrum (unif (1 / 2)) x) ^ 4 := by
    convert hp using 1 <;> ring
  have hbase := (pow_left_inj₀
    (mul_nonneg (sq_nonneg _) (shellSpectrum_nonneg _))
    (mul_nonneg (sq_nonneg _) (shellSpectrum_nonneg _)) (by norm_num : (4 : ℕ) ≠ 0)).mp hfour
  have hpow := congrArg (fun z : ℝ => z ^ (n + 4)) hbase
  simpa only [cardinalSpline, shellSpectrum_upow, mul_pow, ← pow_mul,
    Nat.add_assoc, Nat.reduceAdd] using hpow

theorem aliasDensity_cardinal_add_nat (n j : ℕ) {ε : ℝ} (hε : 0 < ε) :
    aliasDensity (cardinalSpline n) ((j : ℝ) + ε) =
      (ε / ((j : ℝ) + ε)) ^ (2 * (n + 4)) * aliasDensity (cardinalSpline n) ε := by
  have hs : 0 < (j : ℝ) + ε := add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) hε
  have hterm : ∀ k : ℕ,
      shellSpectrum (cardinalSpline n) (((k : ℝ) + 1) * ((j : ℝ) + ε)) =
        (ε / ((j : ℝ) + ε)) ^ (2 * (n + 4)) *
          shellSpectrum (cardinalSpline n) (((k : ℝ) + 1) * ε) := by
    intro k
    have hp := weighted_cardinalSpectrum_add_int n (((k + 1) * j : ℕ) : ℤ)
      (((k : ℝ) + 1) * ε)
    have ha : ((((k + 1) * j : ℕ) : ℤ) : ℝ) + ((k : ℝ) + 1) * ε =
        ((k : ℝ) + 1) * ((j : ℝ) + ε) := by push_cast; ring
    rw [ha] at hp
    have hk : ((k : ℝ) + 1) ^ (2 * (n + 4)) ≠ 0 := by positivity
    have he : ((j : ℝ) + ε) ^ (2 * (n + 4)) *
        shellSpectrum (cardinalSpline n) (((k : ℝ) + 1) * ((j : ℝ) + ε)) =
      ε ^ (2 * (n + 4)) * shellSpectrum (cardinalSpline n) (((k : ℝ) + 1) * ε) := by
      apply mul_left_cancel₀ hk
      simpa only [mul_pow, mul_assoc] using hp
    rw [div_pow]
    field_simp [hs.ne']
    simpa only [mul_comm (shellSpectrum _ _) _] using he
  unfold aliasDensity
  simp_rw [hterm]
  exact tsum_mul_left

private theorem phase_norm_sq (t : ℝ) :
    ‖1 - Complex.exp (I * (t : ℂ))‖ ^ 2 =
      t ^ 2 * ‖paperFT (fun u => (unif (1 / 2) u : ℂ)) (t : ℂ)‖ ^ 2 := by
  by_cases ht : t = 0
  · simp [ht]
  have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht
  have hu := RHTower.WeilDeletion.paperFT_unif (by norm_num : (0 : ℝ) < 1 / 2) htc
  have hden : (2 : ℂ) * I * t * (1 / 2) = I * t := by ring
  have hhalf : I * (t : ℂ) * (1 / 2) = I * t / 2 := by ring
  norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] at hu
  rw [hden, hhalf] at hu
  have hnum : Complex.exp (I * (t : ℂ) / 2) - Complex.exp (-(I * t / 2)) =
      Complex.exp (-(I * t / 2)) * (Complex.exp (I * t) - 1) := by
    rw [mul_sub, ← Complex.exp_add, mul_one]
    congr 1
    congr 1
    ring
  have hre : (-(I * (t : ℂ) / 2)).re = 0 := by simp
  rw [hu, hnum, norm_div, norm_mul, Complex.norm_exp, hre, Real.exp_zero, one_mul,
    norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, div_pow, sq_abs]
  rw [norm_sub_rev (Complex.exp (I * (t : ℂ))) (1 : ℂ)]
  field_simp [ht]

/-- The difference contributes the polynomial multiplier of an iterated derivative. -/
theorem shellSpectrum_differenceSpline_eq_cardinal (n : ℕ) (t : ℝ) :
    shellSpectrum (differenceSpline n) t =
      (2 * Real.pi * t) ^ (2 * n) * shellSpectrum (cardinalSpline n) t := by
  have hp := phase_norm_sq (2 * Real.pi * t)
  unfold shellSpectrum
  rw [paperFT_differenceSpline, cardinalSpline, paperFT_upow, paperFT_upow,
    norm_mul, norm_pow, norm_pow, norm_pow, mul_pow]
  have hpow : (‖1 - Complex.exp (I * ((2 * Real.pi * t : ℝ) : ℂ))‖ ^ n) ^ 2 =
      (‖1 - Complex.exp (I * ((2 * Real.pi * t : ℝ) : ℂ))‖ ^ 2) ^ n := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm n 2]
  rw [hpow, hp, mul_pow]
  simp only [← pow_mul, Nat.reduceAdd]
  rw [mul_assoc, ← pow_add]
  congr 1
  congr 1
  omega

/-- Nonzero integral and unbounded harmonic-zero multiplicity coexist with quartic decay. -/
theorem shellSpectrum_unitNotchProfile_eq_cardinal (r : ℕ) (t : ℝ) :
    shellSpectrum (unitNotchProfile r) t =
      (1 + (2 * Real.pi * t) ^ (4 * r + 2)) *
        shellSpectrum (cardinalSpline (2 * r + 1)) t := by
  rw [shellSpectrum_unitNotchProfile, shellSpectrum_differenceSpline_eq_cardinal,
    show 2 * (2 * r + 1) = 4 * r + 2 by omega]
  ring

/-- The unit-mass profile has one seventh-order term and a higher-order cardinal term. -/
theorem aliasDensity_unitNotchProfile_near_integer (r j : ℕ) {ε : ℝ}
    (hε : 0 < ε) (hgap : 8 * (r : ℝ) + 8 < 1 / ε) :
    aliasDensity (unitNotchProfile r) ((j : ℝ) + ε) =
      (∫ u, differenceSpline (2 * r + 1) u ^ 2) * ε ^ 7 / (2 * ((j : ℝ) + ε) ^ 8) +
        (ε / ((j : ℝ) + ε)) ^ (4 * r + 10) *
          ((∫ u, cardinalSpline (2 * r + 1) u ^ 2) / (2 * ε) - 1 / 2) := by
  have hs : 0 < (j : ℝ) + ε := add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) hε
  have hgapb : 2 * (2 * ((2 * r + 1 : ℕ) : ℝ) + 2) < 1 / ε := by
    push_cast
    linarith only [hgap]
  have hgapd : 2 * ((2 * r + 1 : ℕ) + (2 : ℝ)) < 1 / ε := by
    have hr := Nat.cast_nonneg (α := ℝ) r
    push_cast
    linarith only [hgap, hr]
  rw [aliasDensity_unitNotchProfile r hs, aliasDensity_cardinal_add_nat _ _ hε,
    aliasDensity_below_spacing (contDiff_cardinalSpline (2 * r + 1))
      (fun _ hu => cardinalSpline_support _ hu) hε hgapb,
    integral_cardinalSpline, one_pow,
    aliasDensity_differenceSpline_near_integer (2 * r) j hε hgapd]
  rw [show 2 * (2 * r + 1 + 4) = 4 * r + 10 by omega]
  ring

theorem aliasDensity_unitNotchProfile_div_pow_seven (r j : ℕ) {ε : ℝ}
    (hε : 0 < ε) (hgap : 8 * (r : ℝ) + 8 < 1 / ε) :
    aliasDensity (unitNotchProfile r) ((j : ℝ) + ε) / ε ^ 7 =
      (∫ u, differenceSpline (2 * r + 1) u ^ 2) / (2 * ((j : ℝ) + ε) ^ 8) +
        ε ^ (4 * r + 2) * ((∫ u, cardinalSpline (2 * r + 1) u ^ 2) - ε) /
          (2 * ((j : ℝ) + ε) ^ (4 * r + 10)) := by
  have hs : 0 < (j : ℝ) + ε := add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) hε
  rw [aliasDensity_unitNotchProfile_near_integer r j hε hgap, div_pow]
  have he : ε ^ (4 * r + 10) = ε ^ (4 * r + 2) * ε ^ 8 := by
    rw [show 4 * r + 10 = (4 * r + 2) + 8 by omega, pow_add]
  rw [he]
  field_simp [hε.ne', hs.ne']

/-- Restoring integral one preserves the exact seventh-order asymptotic. -/
theorem tendsto_unitNotchProfile_alias_div_pow_seven (r j : ℕ) :
    Tendsto (fun ε : ℝ => aliasDensity (unitNotchProfile r) ((j + 1 : ℕ) + ε) / ε ^ 7)
      (𝓝[>] 0)
      (𝓝 ((∫ u, differenceSpline (2 * r + 1) u ^ 2) / (2 * ((j + 1 : ℕ) : ℝ) ^ 8))) := by
  let D := ∫ u, differenceSpline (2 * r + 1) u ^ 2
  let B := ∫ u, cardinalSpline (2 * r + 1) u ^ 2
  let J : ℝ := (j + 1 : ℕ)
  have hJ : 0 < J := by dsimp only [J]; positivity
  have hA : 0 < 8 * (r : ℝ) + 8 := by positivity
  let F : ℝ → ℝ := fun ε => D / (2 * (J + ε) ^ 8) +
    ε ^ (4 * r + 2) * (B - ε) / (2 * (J + ε) ^ (4 * r + 10))
  have hc : ContinuousAt F 0 := by
    apply ContinuousAt.add
    · exact continuousAt_const.div
        (continuousAt_const.mul ((continuousAt_const.add continuousAt_id).pow 8))
        (by dsimp; positivity)
    · exact ((continuousAt_id.pow (4 * r + 2)).mul
        (continuousAt_const.sub continuousAt_id)).div
        (continuousAt_const.mul ((continuousAt_const.add continuousAt_id).pow (4 * r + 10)))
        (by dsimp; positivity)
  have ht : Tendsto F (𝓝[>] 0) (𝓝 (D / (2 * J ^ 8))) := by
    simpa only [F, add_zero, zero_pow (by omega : 4 * r + 2 ≠ 0), zero_mul, zero_div]
      using hc.tendsto.mono_left nhdsWithin_le_nhds
  change Tendsto _ _ (𝓝 (D / (2 * J ^ 8)))
  apply ht.congr'
  have hsmall : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε < 1 / (8 * (r : ℝ) + 8) :=
    (eventually_lt_nhds (one_div_pos.mpr hA)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hsmall] with ε hε hsmallε
  have hε0 : 0 < ε := hε
  have hgap : 8 * (r : ℝ) + 8 < 1 / ε := by
    apply (lt_div_iff₀ hε0).mpr
    have he := (lt_div_iff₀ hA).mp hsmallε
    linarith only [he]
  rw [aliasDensity_unitNotchProfile_div_pow_seven r (j + 1) hε0 hgap]

theorem unitNotchProfile_alias_coefficient_pos (r j : ℕ) :
    0 < (∫ u, differenceSpline (2 * r + 1) u ^ 2) / (2 * ((j + 1 : ℕ) : ℝ) ^ 8) :=
  div_pos (integral_differenceSpline_sq_pos _) (by positivity)

#print axioms integral_unitNotchProfile
#print axioms shellSpectrum_unitNotchProfile
#print axioms shellSpectrum_unitNotchProfile_eq_cardinal
#print axioms aliasDensity_unitNotchProfile_near_integer
#print axioms tendsto_unitNotchProfile_alias_div_pow_seven
#print axioms unitNotchProfile_alias_coefficient_pos

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.SplineAliasNotches
