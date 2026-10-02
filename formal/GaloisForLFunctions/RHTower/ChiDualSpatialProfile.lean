import GaloisForLFunctions.RHTower.ChiDualSpatialStationary
import GaloisForLFunctions.RHTower.ZetaChiNormalizedShiftBound
import GaloisForLFunctions.RHTower.ZetaChiConductorOrientation
import GaloisForLFunctions.RHTower.SmoothAFECofactorCellStability
import Mathlib.Order.Filter.AtTopBot.Ring

/-!
# Deterministic Gaussian profile of a complete dual integer block

All high Fourier modes have a complete paired tail estimate. Every nonnegative
spatial mode is nonstationary, leaving the negative first mode. Its literal
stationary coefficient has a chi phase that cancels to one, so the Gaussian
cutoff survives as the full block's interior scalar profile.

On N = m^10 with spatial margin m^6, the error is O(1/m), uniformly on each
fixed right-strip disc. Both transition bands remain outside this interior claim.
-/

open Complex Set Filter Topology MeasureTheory
open scoped BigOperators
noncomputable section
namespace RHTower



/-- The exact chi-scaled, unsmoothed spatial saddle coefficient. -/
def chiDualSpatialSaddleCoefficient (s : ℂ) (a : ℝ) : ℂ :=
  zetaChi (s + ((2 * Real.pi * a : ℝ) : ℂ) * I) *
    (a : ℂ) ^ (s - 1) * (Real.sqrt a : ℂ) *
    bourgainOscillation (chiDualSpatialPhase (2 * Real.pi * a) (-(2 * Real.pi)) a - Real.pi / 4)

private theorem spatial_power_mul_sqrt (s : ℂ) {a : ℝ} (ha : 0 < a) :
    (a : ℂ) ^ (s - 1) * (Real.sqrt a : ℂ) =
      Complex.exp ((s - (1 / 2 : ℂ)) * (Real.log a : ℂ)) := by
  have hsqrt : (Real.sqrt a : ℂ) = Complex.exp ((Real.log a : ℂ) / 2) := by
    have he : Real.exp (Real.log a / 2) = Real.sqrt a := by
      rw [← Real.log_sqrt ha.le, Real.exp_log (Real.sqrt_pos.mpr ha)]
    rw [← he, Complex.ofReal_exp]
    congr 1
    push_cast
    rfl
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr ha.ne'),
    ← Complex.ofReal_log ha.le, hsqrt, ← Complex.exp_add]
  congr 1
  ring

/-- The reversed spatial Fresnel direction cancels the actual critical chi
orientation, with its complete reciprocal-height remainder. -/
theorem norm_chiDualSpatial_critical_saddle_sub_one_le {a : ℝ}
    (ht : 4 ≤ 2 * Real.pi * a) :
    ‖zetaChi (linePt (2 * Real.pi * a)) *
      bourgainOscillation (chiDualSpatialPhase (2 * Real.pi * a) (-(2 * Real.pi)) a - Real.pi / 4) - 1‖ ≤
      26 / (2 * Real.pi * a) := by
  let t := 2 * Real.pi * a
  let E := bourgainOscillation (chiDualSpatialPhase t (-(2 * Real.pi)) a - Real.pi / 4)
  let M := bourgainOscillation (Real.pi / 4) *
    Complex.exp (((t - t * Real.log (t / (2 * Real.pi)) : ℝ) : ℂ) * I)
  have hb : ‖zetaChi (linePt t) - M‖ ≤ 26 / t := by
    simpa only [Int.cast_one, zpow_one, abs_one, one_mul, mul_one] using
      norm_zetaChi_integerGrade_sub_explicit_model_le 1 ht
  have hprod : M * E = 1 := by
    dsimp only [M, E, bourgainOscillation, chiDualSpatialPhase, t]
    have hd : (2 * Real.pi * a) / (2 * Real.pi) = a := by field_simp
    rw [hd, ← Complex.exp_add, ← Complex.exp_add]
    have he : I * ((Real.pi / 4 : ℝ) : ℂ) +
        (((2 * Real.pi * a - 2 * Real.pi * a * Real.log a : ℝ) : ℂ) * I) +
        I * ((2 * Real.pi * a * Real.log a + -(2 * Real.pi) * a - Real.pi / 4 : ℝ) : ℂ) = 0 := by
      push_cast
      ring
    rw [he, Complex.exp_zero]
  change ‖zetaChi (linePt t) * E - 1‖ ≤ _
  rw [← hprod, ← sub_mul, norm_mul]
  have hE : ‖E‖ = 1 := norm_bourgainOscillation _
  rw [hE, mul_one]
  exact hb

/-- The actual spatial saddle has unit leading coefficient throughout the
open strip, with source-derived conductor and compact-shift errors. -/
theorem norm_chiDualSpatialSaddleCoefficient_sub_one_le {s : ℂ} {a : ℝ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1) (ha : 0 < a)
    (ht : 4 ≤ 2 * Real.pi * a) (him : 2 * |s.im| ≤ 2 * Real.pi * a)
    (hsize : 26 * ‖s - (1 / 2 : ℂ)‖ + 10 * ‖s - (1 / 2 : ℂ)‖ ^ 2 ≤ 2 * Real.pi * a) :
    ‖chiDualSpatialSaddleCoefficient s a - 1‖ ≤
      (52 * ‖s - (1 / 2 : ℂ)‖ + 20 * ‖s - (1 / 2 : ℂ)‖ ^ 2 + 26) / (2 * Real.pi * a) := by
  let t := 2 * Real.pi * a
  let R : ℂ := (zetaChi (s + (t : ℂ) * I) / zetaChi (linePt t)) *
    Complex.exp ((s - (1 / 2 : ℂ)) * (Real.log a : ℂ))
  let H : ℂ := zetaChi (linePt t) *
    bourgainOscillation (chiDualSpatialPhase t (-(2 * Real.pi)) a - Real.pi / 4)
  have hr : ‖R - 1‖ ≤ (52 * ‖s - (1 / 2 : ℂ)‖ + 20 * ‖s - (1 / 2 : ℂ)‖ ^ 2) / t := by
    have hb := norm_zetaChi_normalized_shift_sub_one_le hs0 hs1 ht him hsize
    have hd : (2 * Real.pi * a) / (2 * Real.pi) = a := by field_simp
    simpa only [hd] using hb
  have hH : ‖H‖ = 1 := by
    dsimp only [H]
    rw [norm_mul, norm_zetaChi_line, norm_bourgainOscillation, mul_one]
  have hH1 : ‖H - 1‖ ≤ 26 / t := norm_chiDualSpatial_critical_saddle_sub_one_le ht
  have he : chiDualSpatialSaddleCoefficient s a = R * H := by
    unfold chiDualSpatialSaddleCoefficient
    rw [mul_assoc (zetaChi _) ((a : ℂ) ^ (s - 1)), spatial_power_mul_sqrt s ha]
    dsimp only [R, H, t]
    field_simp [zetaChi_line_ne_zero]
  rw [he]
  calc
    _ = ‖(R - 1) * H + (H - 1)‖ := by congr 1; ring
    _ ≤ ‖(R - 1) * H‖ + ‖H - 1‖ := norm_add_le _ _
    _ = ‖R - 1‖ + ‖H - 1‖ := by rw [norm_mul, hH, mul_one]
    _ ≤ (52 * ‖s - (1 / 2 : ℂ)‖ + 20 * ‖s - (1 / 2 : ℂ)‖ ^ 2) / t + 26 / t := add_le_add hr hH1
    _ = _ := by dsimp only [t]; ring

/-- The literal Gaussian cutoff survives as the spatial saddle profile. -/
theorem norm_chiDualSpatial_smoothed_saddle_sub_cutoff_le {s : ℂ} {N a : ℝ}
    (hN : 0 < N) (hs0 : 0 < s.re) (hs1 : s.re < 1) (ha : 0 < a)
    (ht : 4 ≤ 2 * Real.pi * a) (him : 2 * |s.im| ≤ 2 * Real.pi * a)
    (hsize : 26 * ‖s - (1 / 2 : ℂ)‖ + 10 * ‖s - (1 / 2 : ℂ)‖ ^ 2 ≤ 2 * Real.pi * a) :
    ‖smoothAFECutoff (a / N) * chiDualSpatialSaddleCoefficient s a - smoothAFECutoff (a / N)‖ ≤
      (52 * ‖s - (1 / 2 : ℂ)‖ + 20 * ‖s - (1 / 2 : ℂ)‖ ^ 2 + 26) / (2 * Real.pi * a) := by
  have hb := norm_chiDualSpatialSaddleCoefficient_sub_one_le hs0 hs1 ha ht him hsize
  have he : smoothAFECutoff (a / N) * chiDualSpatialSaddleCoefficient s a - smoothAFECutoff (a / N) =
      smoothAFECutoff (a / N) * (chiDualSpatialSaddleCoefficient s a - 1) := by ring
  rw [he, norm_mul]
  calc
    _ ≤ 1 * ‖chiDualSpatialSaddleCoefficient s a - 1‖ :=
      mul_le_mul_of_nonneg_right (norm_smoothAFECutoff_le_one (div_pos ha hN)) (norm_nonneg _)
    _ ≤ _ := by simpa only [one_mul] using hb


/-- Every nonnegative spatial Fourier frequency is nonstationary on the
full literal block. Both boundaries and the whole repeated-IBP remainder
are retained in a compact-uniform estimate. -/
theorem exists_chiDualSpatial_nonnegative_mode_bound (c : ℂ) (r : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ s ∈ Metric.closedBall c r, ∀ N : ℝ, 50 ≤ N →
      ∀ t : ℝ, N ≤ t ∧ t ≤ 2 * N →
      ∀ a b : ℝ, N / 5 - 1 / 2 ≤ a → b ≤ 6 * N / 25 + 1 / 2 → a ≤ b →
      ∀ w : ℝ, 0 ≤ w →
      ‖∫ x in a..b, chiDualSpatialSlowAmplitude s N x *
        Complex.exp (I * (chiDualSpatialPhase t w x : ℂ))‖ ≤ C * N ^ (s.re - 1) := by
  obtain ⟨C, hC, hj⟩ := exists_chiDualSpatialSlowJets_bound c r
  refine ⟨500000 * C, by positivity, ?_⟩
  intro s hs N hN t ht a b ha hb hab w hw
  have hN0 : 0 < N := by linarith
  have ha0 : 0 < a := by linarith
  have hlen : b - a ≤ N := by linarith
  let U := C * N ^ (s.re - 1)
  let L := 804 * U / N
  let R := 490404 * U / N ^ 2
  have hU : 0 ≤ U := mul_nonneg hC.le (Real.rpow_nonneg hN0.le _)
  have hxx (x : ℝ) (hx : x ∈ Icc a b) :
      N / 5 - 1 / 2 ≤ x ∧ x ≤ 6 * N / 25 + 1 / 2 :=
    ⟨ha.trans hx.1, hx.2.trans hb⟩
  have hg (x : ℝ) (hx : x ∈ Icc a b) : 1 ≤ chiDualSpatialPhaseSlope t w x := by
    have hh := (chiDual_spatial_block_ratio_bounds hN ht (hxx x hx)).2.2.2.1
    dsimp only [chiDualSpatialPhaseSlope]
    linarith
  have hg0 (x : ℝ) (hx : x ∈ Icc a b) : chiDualSpatialPhaseSlope t w x ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one (hg x hx))
  have hp (x : ℝ) (hx : x ∈ Icc a b) :
      ‖chiDualSpatialIBPFirst s N t w x‖ ≤ U ∧
      ‖chiDualSpatialIBPSecond s N t w x‖ ≤ L ∧
      ‖chiDualSpatialIBPRemainder s N t w x‖ ≤ R := by
    obtain ⟨hx0, hxlo, hxhi, _, _⟩ := chiDual_spatial_block_ratio_bounds hN ht (hxx x hx)
    have hxn : x / N ∈ Icc (1 / 6 : ℝ) (1 / 3) := by
      constructor
      · apply (le_div_iff₀ hN0).mpr
        linarith
      · apply (div_le_iff₀ hN0).mpr
        linarith
    obtain ⟨hv, hv1, hv2⟩ := hj s hs N hN0 x hxn
    have hgn : ‖(chiDualSpatialPhaseSlope t w x : ℂ)‖ = chiDualSpatialPhaseSlope t w x := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_trans zero_le_one (hg x hx))]
    obtain ⟨h1, h2⟩ := chiDual_spatial_phase_derivative_bounds hN ht (hxx x hx)
    have hg1 : ‖(chiDualSpatialPhaseSecond t x : ℂ)‖ ≤ 100 / N := by
      simpa only [chiDualSpatialPhaseSecond, Complex.norm_real, Real.norm_eq_abs] using h1
    have hg2 : ‖(chiDualSpatialPhaseThird t x : ℂ)‖ ≤ 1000 / N ^ 2 := by
      simpa only [chiDualSpatialPhaseThird, Complex.norm_real, Real.norm_eq_abs] using h2
    have hhalf : (1 : ℝ) / 2 ≤ ‖(chiDualSpatialPhaseSlope t w x : ℂ)‖ := by
      rw [hgn]
      linarith [hg x hx]
    refine ⟨?_, ?_, ?_⟩
    · dsimp only [chiDualSpatialIBPFirst, chiDualIBPFirst]
      rw [norm_div, norm_mul, norm_I, one_mul, hgn]
      exact (div_le_div_of_nonneg_right hv (by linarith [hg x hx])).trans
        (div_le_self hU (hg x hx))
    · have hh := norm_chiDualIBPSecond_scaled_le hU hN0 (le_refl (1 : ℝ)) hv hv1 hhalf hg1
      simpa only [chiDualSpatialIBPSecond, L, one_pow, mul_one] using hh
    · have hh := norm_chiDualIBPRemainder_scaled_le hU hN0 (le_refl (1 : ℝ)) hv hv1 hv2 hhalf hg1 hg2
      simpa only [chiDualSpatialIBPRemainder, R, one_pow, mul_one] using hh
  let E : ℝ → ℂ := fun x => Complex.exp (I * (chiDualSpatialPhase t w x : ℂ))
  have hE (x : ℝ) : ‖E x‖ = 1 := Complex.norm_exp_I_mul_ofReal _
  have hboundary (x : ℝ) (hx : x ∈ Icc a b) :
      ‖(chiDualSpatialIBPFirst s N t w x - chiDualSpatialIBPSecond s N t w x) * E x‖ ≤ U + L := by
    rw [norm_mul, hE, mul_one]
    exact (norm_sub_le _ _).trans (add_le_add (hp x hx).1 (hp x hx).2.1)
  have hrem : ‖∫ x in a..b, chiDualSpatialIBPRemainder s N t w x * E x‖ ≤ R * N := by
    have hi : ‖∫ x in a..b, chiDualSpatialIBPRemainder s N t w x * E x‖ ≤ R * |b - a| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro x hx
      rw [uIoc_of_le hab] at hx
      simpa only [norm_mul, hE, mul_one] using (hp x ⟨hx.1.le, hx.2⟩).2.2
    rw [abs_of_nonneg (sub_nonneg.mpr hab)] at hi
    exact hi.trans (mul_le_mul_of_nonneg_left hlen (by dsimp only [R]; positivity))
  rw [integral_chiDualSpatial_eq_two_boundaries s hN0 ha0 hab t w hg0]
  calc
    _ ≤ ‖(chiDualSpatialIBPFirst s N t w b - chiDualSpatialIBPSecond s N t w b) * E b‖ +
        ‖(chiDualSpatialIBPFirst s N t w a - chiDualSpatialIBPSecond s N t w a) * E a‖ +
        ‖∫ x in a..b, chiDualSpatialIBPRemainder s N t w x * E x‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ (U + L) + (U + L) + R * N :=
      add_le_add (add_le_add (hboundary b ⟨hab, le_rfl⟩) (hboundary a ⟨le_rfl, hab⟩)) hrem
    _ = 2 * U + 492012 * U / N := by dsimp only [L, R]; field_simp; ring
    _ ≤ 2 * U + 492012 * U := by
      apply add_le_add le_rfl
      exact div_le_self (by positivity) (by linarith)
    _ ≤ 500000 * U := by nlinarith
    _ = _ := by dsimp only [U]; ring


private theorem integral_spatialAmplitude_eq_zero_mode (s : ℂ) {N a b : ℝ}
    (hN : 0 < N) (ha : 0 < a) (hab : a ≤ b) (t : ℝ) :
    (∫ x in a..b, zetaChiDualSpatialAmplitude s N t x) =
      ∫ x in a..b, chiDualSpatialSlowAmplitude s N x *
        Complex.exp (I * (chiDualSpatialPhase t 0 x : ℂ)) := by
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le hab] at hx
  dsimp only
  rw [zetaChiDualSpatialAmplitude_eq_slow s hN (ha.trans_le hx.1) t]
  simp only [chiDualSpatialPhase, zero_mul, add_zero, bourgainOscillation]

/-- The entire literal dual integer block reduces to its negative first
spatial Fourier mode, with every other mode charged a uniform source error. -/
theorem exists_chiDual_integer_block_single_mode_error (c : ℂ) (r : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ s ∈ Metric.closedBall c r, ∀ N : ℝ, 50 ≤ N →
      ∀ t : ℝ, N ≤ t ∧ t ≤ 2 * N →
      ∀ A B : ℕ, N / 5 ≤ (A : ℝ) → (B : ℝ) ≤ 6 * N / 25 → A ≤ B →
      ‖(∑ n ∈ Finset.Icc A B, smoothAFECutoff ((n : ℝ) / N) * zetaChiDualInteriorAtom s n t) -
        zetaChi (s + (t : ℂ) * I) *
          (∫ x in ((A : ℝ) - 1 / 2)..((B : ℝ) + 1 / 2), chiDualSpatialSlowAmplitude s N x *
            Complex.exp (I * (chiDualSpatialPhase t (-(2 * Real.pi)) x : ℂ)))‖ ≤
        C * N ^ (s.re - 1) * ‖zetaChi (s + (t : ℂ) * I)‖ := by
  obtain ⟨C₀, hC₀, htail⟩ := exists_chiDual_integer_block_low_modes_error c r
  obtain ⟨C₁, hC₁, hpos⟩ := exists_chiDualSpatial_nonnegative_mode_bound c r
  refine ⟨C₀ + 2 * C₁, by positivity, ?_⟩
  intro s hs N hN t ht A B hA hB hAB
  have hN0 : 0 < N := by linarith
  let a : ℝ := (A : ℝ) - 1 / 2
  let b : ℝ := (B : ℝ) + 1 / 2
  let q : ℂ := zetaChi (s + (t : ℂ) * I)
  let J : ℝ → ℂ := fun w => ∫ x in a..b, chiDualSpatialSlowAmplitude s N x *
    Complex.exp (I * (chiDualSpatialPhase t w x : ℂ))
  let S : ℂ := ∑ n ∈ Finset.Icc A B, smoothAFECutoff ((n : ℝ) / N) * zetaChiDualInteriorAtom s n t
  have ha : N / 5 - 1 / 2 ≤ a := by dsimp only [a]; linarith
  have hb : b ≤ 6 * N / 25 + 1 / 2 := by dsimp only [b]; linarith
  have ha0 : 0 < a := by linarith
  have hab : a ≤ b := by
    have hABR : (A : ℝ) ≤ B := by exact_mod_cast hAB
    dsimp only [a, b]
    linarith
  have he : chiDualLowSpatialModes s N t A B = q * (J 0 + (J (2 * Real.pi) + J (-(2 * Real.pi)))) := by
    have hcos := chiDualSpatial_cos_integral_eq_pair s hN0 ha0 hab t 1
    simp only [Nat.cast_one, mul_one] at hcos
    dsimp only [chiDualLowSpatialModes, q]
    rw [hcos, integral_spatialAmplitude_eq_zero_mode s hN0 ha0 hab t]
  have h0 : ‖J 0‖ ≤ C₁ * N ^ (s.re - 1) :=
    hpos s hs N hN t ht a b ha hb hab 0 le_rfl
  have h1 : ‖J (2 * Real.pi)‖ ≤ C₁ * N ^ (s.re - 1) :=
    hpos s hs N hN t ht a b ha hb hab (2 * Real.pi) (by positivity)
  have herror : ‖S - q * (J 0 + (J (2 * Real.pi) + J (-(2 * Real.pi))))‖ ≤
      C₀ * N ^ (s.re - 1) * ‖q‖ := by
    simpa only [he] using htail s hs N hN t ht A B hA hB hAB
  change ‖S - q * J (-(2 * Real.pi))‖ ≤ _
  calc
    _ = ‖(S - q * (J 0 + (J (2 * Real.pi) + J (-(2 * Real.pi))))) +
        q * (J 0 + J (2 * Real.pi))‖ := by congr 1; ring
    _ ≤ ‖S - q * (J 0 + (J (2 * Real.pi) + J (-(2 * Real.pi))))‖ +
        ‖q * (J 0 + J (2 * Real.pi))‖ := norm_add_le _ _
    _ ≤ C₀ * N ^ (s.re - 1) * ‖q‖ + ‖q‖ * (2 * C₁ * N ^ (s.re - 1)) := by
      apply add_le_add herror
      rw [norm_mul]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      calc
        _ ≤ ‖J 0‖ + ‖J (2 * Real.pi)‖ := norm_add_le _ _
        _ ≤ C₁ * N ^ (s.re - 1) + C₁ * N ^ (s.re - 1) := add_le_add h0 h1
        _ = _ := by ring
    _ = _ := by dsimp only [q]; ring

/-- Exact identification of the literal chi-scaled saddle with the cutoff
times its conductor-normalized scalar coefficient. -/
theorem chiDualSpatial_actual_saddle_eq_cutoff_coefficient (s : ℂ) {N a : ℝ}
    (hN : 0 < N) (ha : 0 < a) :
    zetaChi (s + ((2 * Real.pi * a : ℝ) : ℂ) * I) *
      ((chiDualSpatialSlowAmplitude s N a *
        ((Real.sqrt a : ℂ) * bourgainOscillation (-(Real.pi / 4)))) *
        Complex.exp (I * (chiDualSpatialPhase (2 * Real.pi * a) (-(2 * Real.pi)) a : ℂ))) =
      smoothAFECutoff (a / N) * chiDualSpatialSaddleCoefficient s a := by
  rw [chiDualSpatialSlowAmplitude_eq s hN ha]
  unfold chiDualSpatialSaddleCoefficient bourgainOscillation
  have he : Complex.exp (I * ((chiDualSpatialPhase (2 * Real.pi * a) (-(2 * Real.pi)) a - Real.pi / 4 : ℝ) : ℂ)) =
      Complex.exp (I * ((-(Real.pi / 4) : ℝ) : ℂ)) *
        Complex.exp (I * (chiDualSpatialPhase (2 * Real.pi * a) (-(2 * Real.pi)) a : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [he]
  ring

/-- The full literal dual integer block has the Gaussian scalar profile at
an interior spatial saddle. Every Fourier mode, endpoint and stationary
remainder is included in the displayed error; no target-event bound is assumed. -/
theorem exists_chiDual_integer_block_interior_profile (c : ℂ) (r : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ s ∈ Metric.closedBall c r, 0 < s.re → s.re < 1 →
      ∀ N : ℝ, 50 ≤ N → ∀ a : ℝ, 0 < a →
      N ≤ 2 * Real.pi * a ∧ 2 * Real.pi * a ≤ 2 * N →
      2 * |s.im| ≤ 2 * Real.pi * a →
      26 * ‖s - (1 / 2 : ℂ)‖ + 10 * ‖s - (1 / 2 : ℂ)‖ ^ 2 ≤ 2 * Real.pi * a →
      ∀ h : ℝ, 0 < h → h ≤ a / 2 →
      ∀ A B : ℕ, N / 5 ≤ (A : ℝ) → (B : ℝ) ≤ 6 * N / 25 → A ≤ B →
      (A : ℝ) - 1 / 2 ≤ a - h → a + h ≤ (B : ℝ) + 1 / 2 →
      ‖(∑ n ∈ Finset.Icc A B, smoothAFECutoff ((n : ℝ) / N) *
          zetaChiDualInteriorAtom s n (2 * Real.pi * a)) - smoothAFECutoff (a / N)‖ ≤
        C * N ^ (s.re - 1) * ‖zetaChi (s + ((2 * Real.pi * a : ℝ) : ℂ) * I)‖ *
          (1 + (2 * h ^ 2 / N + 20 * a ^ 2 / (N * Real.pi * h) +
            4 * Real.pi * h ^ 4 / a ^ 2 + 20 * a / (Real.pi * h))) +
        (52 * ‖s - (1 / 2 : ℂ)‖ + 20 * ‖s - (1 / 2 : ℂ)‖ ^ 2 + 26) / (2 * Real.pi * a) := by
  obtain ⟨C₀, hC₀, herr⟩ := exists_chiDual_integer_block_single_mode_error c r
  obtain ⟨C₁, hC₁, hstat⟩ := exists_chiDualSpatial_first_mode_stationary_bound c r
  refine ⟨C₀ + C₁, add_pos hC₀ hC₁, ?_⟩
  intro s hs hs0 hs1 N hN a ha ht him hsize h hh hha A B hA hB hAB hlh hhu
  have hN0 : 0 < N := by linarith
  have ht4 : 4 ≤ 2 * Real.pi * a := by linarith [ht.1]
  let l : ℝ := (A : ℝ) - 1 / 2
  let u : ℝ := (B : ℝ) + 1 / 2
  let q : ℂ := zetaChi (s + ((2 * Real.pi * a : ℝ) : ℂ) * I)
  let S : ℂ := ∑ n ∈ Finset.Icc A B, smoothAFECutoff ((n : ℝ) / N) *
    zetaChiDualInteriorAtom s n (2 * Real.pi * a)
  let J : ℂ := ∫ x in l..u, chiDualSpatialSlowAmplitude s N x *
    Complex.exp (I * (chiDualSpatialPhase (2 * Real.pi * a) (-(2 * Real.pi)) x : ℂ))
  let M : ℂ := (chiDualSpatialSlowAmplitude s N a *
    ((Real.sqrt a : ℂ) * bourgainOscillation (-(Real.pi / 4)))) *
    Complex.exp (I * (chiDualSpatialPhase (2 * Real.pi * a) (-(2 * Real.pi)) a : ℂ))
  let D : ℝ := 2 * h ^ 2 / N + 20 * a ^ 2 / (N * Real.pi * h) +
    4 * Real.pi * h ^ 4 / a ^ 2 + 20 * a / (Real.pi * h)
  let K : ℝ := (52 * ‖s - (1 / 2 : ℂ)‖ + 20 * ‖s - (1 / 2 : ℂ)‖ ^ 2 + 26) / (2 * Real.pi * a)
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have h0 : ‖S - q * J‖ ≤ C₀ * N ^ (s.re - 1) * ‖q‖ :=
    herr s hs N hN (2 * Real.pi * a) ht A B hA hB hAB
  have h1 : ‖J - M‖ ≤ C₁ * N ^ (s.re - 1) * D :=
    hstat s hs N hN a ha ht h l u hh hha
      (by dsimp only [l]; linarith) (by dsimp only [u]; linarith) hlh hhu
  have h2 : ‖q * M - smoothAFECutoff (a / N)‖ ≤ K := by
    rw [show q * M = smoothAFECutoff (a / N) * chiDualSpatialSaddleCoefficient s a from
      chiDualSpatial_actual_saddle_eq_cutoff_coefficient s hN0 ha]
    exact norm_chiDualSpatial_smoothed_saddle_sub_cutoff_le hN0 hs0 hs1 ha ht4 him hsize
  change ‖S - smoothAFECutoff (a / N)‖ ≤ _
  calc
    _ = ‖(S - q * J) + q * (J - M) + (q * M - smoothAFECutoff (a / N))‖ := by congr 1; ring
    _ ≤ ‖S - q * J‖ + ‖q * (J - M)‖ + ‖q * M - smoothAFECutoff (a / N)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ C₀ * N ^ (s.re - 1) * ‖q‖ + ‖q‖ * (C₁ * N ^ (s.re - 1) * D) + K := by
      rw [norm_mul]
      exact add_le_add (add_le_add h0 (mul_le_mul_of_nonneg_left h1 (norm_nonneg _))) h2
    _ = (N ^ (s.re - 1) * ‖q‖) * (C₀ + C₁ * D) + K := by ring
    _ ≤ (N ^ (s.re - 1) * ‖q‖) * ((C₀ + C₁) * (1 + D)) + K := by
      apply add_le_add _ le_rfl
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith [mul_nonneg hC₀.le hD]
    _ = _ := by dsimp only [q, D, K]; ring


private theorem spatial_profile_remainder_decay {m a : ℝ} (hm : 1 ≤ m)
    (ha : m ^ 10 / 8 ≤ a) (ha' : a ≤ m ^ 10) :
    (1 / Real.sqrt (m ^ 10)) *
      (1 + (2 * (m ^ 6) ^ 2 / m ^ 10 + 20 * a ^ 2 / (m ^ 10 * Real.pi * m ^ 6) +
        4 * Real.pi * (m ^ 6) ^ 4 / a ^ 2 + 20 * a / (Real.pi * m ^ 6))) ≤ 1067 / m := by
  have hm0 : 0 < m := by linarith
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity) ha
  have hp : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
  have h4 : 1 ≤ m ^ 4 := one_le_pow₀ hm
  have h24 : m ^ 2 ≤ m ^ 4 := by
    have h2 : 1 ≤ m ^ 2 := one_le_pow₀ hm
    nlinarith [mul_nonneg (sub_nonneg.mpr h2) (sq_nonneg m)]
  have hfirst : 2 * (m ^ 6) ^ 2 / m ^ 10 ≤ 2 * m ^ 4 := by
    calc
      _ = 2 * m ^ 2 := by field_simp
      _ ≤ _ := by linarith
  have hsecond : 20 * a ^ 2 / (m ^ 10 * Real.pi * m ^ 6) ≤ 20 * m ^ 4 := by
    calc
      _ ≤ 20 * (m ^ 10) ^ 2 / (m ^ 10 * 1 * m ^ 6) := by gcongr
      _ = _ := by field_simp
  have hthird : 4 * Real.pi * (m ^ 6) ^ 4 / a ^ 2 ≤ 1024 * m ^ 4 := by
    calc
      _ ≤ 4 * 4 * (m ^ 6) ^ 4 / (m ^ 10 / 8) ^ 2 := by
        gcongr
        exact Real.pi_lt_four.le
      _ = _ := by field_simp; ring
  have hfourth : 20 * a / (Real.pi * m ^ 6) ≤ 20 * m ^ 4 := by
    calc
      _ ≤ 20 * m ^ 10 / (1 * m ^ 6) := by gcongr
      _ = _ := by field_simp
  have hsum : 1 + (2 * (m ^ 6) ^ 2 / m ^ 10 + 20 * a ^ 2 / (m ^ 10 * Real.pi * m ^ 6) +
      4 * Real.pi * (m ^ 6) ^ 4 / a ^ 2 + 20 * a / (Real.pi * m ^ 6)) ≤ 1067 * m ^ 4 := by
    linarith
  have hsqrt : Real.sqrt (m ^ 10) = m ^ 5 := by
    rw [show m ^ 10 = (m ^ 5) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  calc
    _ ≤ (1 / Real.sqrt (m ^ 10)) * (1067 * m ^ 4) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by rw [hsqrt]; field_simp

/-- On the polynomial conductor schedule, the complete literal dual block
converges to its Gaussian scalar profile uniformly on each fixed right-strip
disc and every interior physical saddle. The full error is O(1/m). -/
theorem exists_chiDual_integer_block_interior_profile_decay
    (c : ℂ) {r : ℝ} (hr : 0 ≤ r) (hc0 : 1 / 2 ≤ c.re - r) (hc1 : c.re + r < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ m : ℕ in atTop, ∀ s ∈ Metric.closedBall c r,
      ∀ a : ℝ, 0 < a → (m : ℝ) ^ 10 ≤ 2 * Real.pi * a ∧ 2 * Real.pi * a ≤ 2 * (m : ℝ) ^ 10 →
      ∀ A B : ℕ, (m : ℝ) ^ 10 / 5 ≤ A → (B : ℝ) ≤ 6 * (m : ℝ) ^ 10 / 25 → A ≤ B →
      (A : ℝ) - 1 / 2 ≤ a - (m : ℝ) ^ 6 → a + (m : ℝ) ^ 6 ≤ (B : ℝ) + 1 / 2 →
      ‖(∑ n ∈ Finset.Icc A B, smoothAFECutoff ((n : ℝ) / (m : ℝ) ^ 10) *
          zetaChiDualInteriorAtom s n (2 * Real.pi * a)) - smoothAFECutoff (a / (m : ℝ) ^ 10)‖ ≤ C / m := by
  obtain ⟨C₀, hC₀, hprofile⟩ := exists_chiDual_integer_block_interior_profile c r
  obtain ⟨C₁, hC₁, hrow⟩ := exists_reflectedCompactGaussianRow_disc_bounds c hr hc0 hc1
  let R : ℝ := ‖c - (1 / 2 : ℂ)‖ + r
  let J : ℝ := |c.im| + r
  let K : ℝ := 52 * R + 20 * R ^ 2 + 26
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  have hJ : 0 ≤ J := by dsimp only [J]; positivity
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  obtain ⟨M, hM⟩ := exists_nat_gt (50 + 2 * J + 26 * R + 10 * R ^ 2)
  refine ⟨1067 * C₀ * C₁ + K, by positivity, ?_⟩
  have hp : Tendsto (fun m : ℕ => m ^ 10) atTop atTop := tendsto_pow_atTop (by decide)
  filter_upwards [hp.eventually hrow, eventually_ge_atTop M, eventually_ge_atTop (2 : ℕ)] with m hrowm hmM hm2
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm2
  have hm1 : (1 : ℝ) ≤ m := by linarith
  have hm0 : (0 : ℝ) < m := by linarith
  have hMR : (M : ℝ) ≤ m := by exact_mod_cast hmM
  have hmN : (m : ℝ) ≤ (m : ℝ) ^ 10 := by
    have h9 : (1 : ℝ) ≤ (m : ℝ) ^ 9 := one_le_pow₀ hm1
    nlinarith only [mul_nonneg (sub_nonneg.mpr h9) hm0.le]
  have hN : 50 ≤ (m : ℝ) ^ 10 := by
    linarith only [hM, hMR, hmN, hJ, hR, sq_nonneg R]
  have hN0 : 0 < (m : ℝ) ^ 10 := by positivity
  have hm4 : (16 : ℝ) ≤ (m : ℝ) ^ 4 := by
    have h2 : (4 : ℝ) ≤ (m : ℝ) ^ 2 := by
      nlinarith only [hmR, sq_nonneg ((m : ℝ) - 2)]
    nlinarith only [h2, sq_nonneg ((m : ℝ) ^ 2 - 4)]
  have hhN : (m : ℝ) ^ 6 ≤ (m : ℝ) ^ 10 / 16 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hm4) (show (0 : ℝ) ≤ (m : ℝ) ^ 6 by positivity)]
  norm_num only [Nat.cast_pow] at hrowm
  intro s hs a ha ht A B hA hB hAB hlh hhu
  have hre : |s.re - c.re| ≤ r := (by
    simpa only [Complex.sub_re, dist_eq_norm] using Complex.abs_re_le_norm (s - c) :
      |s.re - c.re| ≤ dist s c).trans hs
  have hs0 : 0 < s.re := by linarith only [hc0, (abs_le.mp hre).1]
  have hs1 : s.re < 1 := by linarith only [hc1, (abs_le.mp hre).2]
  have hsc : ‖s - c‖ ≤ r := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hs
  have hd : ‖s - (1 / 2 : ℂ)‖ ≤ R := by
    calc
      _ = ‖(s - c) + (c - (1 / 2 : ℂ))‖ := by congr 1; ring
      _ ≤ ‖s - c‖ + ‖c - (1 / 2 : ℂ)‖ := norm_add_le _ _
      _ ≤ R := by dsimp only [R]; linarith only [hsc]
  have him : |s.im| ≤ J := by
    have he : s.im = (s - c).im + c.im := by simp
    rw [he]
    apply (abs_add_le _ _).trans
    calc
      _ ≤ r + |c.im| := add_le_add ((Complex.abs_im_le_norm (s - c)).trans hsc) le_rfl
      _ = J := by dsimp only [J]; ring
  have hheight : 50 + 2 * J + 26 * R + 10 * R ^ 2 ≤ 2 * Real.pi * a :=
    hM.le.trans (hMR.trans (hmN.trans ht.1))
  have hsize : 26 * ‖s - (1 / 2 : ℂ)‖ + 10 * ‖s - (1 / 2 : ℂ)‖ ^ 2 ≤ 2 * Real.pi * a := by
    calc
      _ ≤ 26 * R + 10 * R ^ 2 := by gcongr
      _ ≤ _ := by linarith only [hheight, hJ]
  have hima : 2 * |s.im| ≤ 2 * Real.pi * a := by
    linarith only [him, hheight, hR, sq_nonneg R]
  have halo : (m : ℝ) ^ 10 / 8 ≤ a := by
    nlinarith only [ht.1, mul_nonneg (sub_nonneg.mpr Real.pi_lt_four.le) ha.le]
  have hahi : a ≤ (m : ℝ) ^ 10 := by
    nlinarith only [ht.2, ha, mul_nonneg (sub_nonneg.mpr Real.pi_gt_three.le) ha.le]
  have hha : (m : ℝ) ^ 6 ≤ a / 2 := by linarith only [hhN, halo]
  have hb := hprofile s hs hs0 hs1 ((m : ℝ) ^ 10) hN a ha ht hima hsize
    ((m : ℝ) ^ 6) (by positivity) hha A B hA hB hAB hlh hhu
  let q : ℂ := zetaChi (s + ((2 * Real.pi * a : ℝ) : ℂ) * I)
  have hnorm : ((m : ℝ) ^ 10) ^ (s.re - 1) * ‖q‖ =
      ‖reflectedCompactGaussianRow s ((m : ℝ) ^ 10) (2 * Real.pi * a)‖ / Real.sqrt ((m : ℝ) ^ 10) := by
    apply (eq_div_iff (Real.sqrt_pos.mpr hN0).ne').mpr
    rw [norm_reflectedCompactGaussianRow s hN0 (2 * Real.pi * a)]
    have he : ((m : ℝ) ^ 10) ^ (s.re - 1) * Real.sqrt ((m : ℝ) ^ 10) =
        ((m : ℝ) ^ 10) ^ (s.re - 1 / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hN0]
      congr 1
      ring
    calc
      _ = ‖q‖ * (((m : ℝ) ^ 10) ^ (s.re - 1) * Real.sqrt ((m : ℝ) ^ 10)) := by ring
      _ = _ := by rw [he]
  have hnormle : ((m : ℝ) ^ 10) ^ (s.re - 1) * ‖q‖ ≤ C₁ / Real.sqrt ((m : ℝ) ^ 10) := by
    rw [hnorm]
    exact div_le_div_of_nonneg_right (hrowm (2 * Real.pi * a) ht s hs).1 (Real.sqrt_nonneg _)
  let D : ℝ := 1 + (2 * ((m : ℝ) ^ 6) ^ 2 / (m : ℝ) ^ 10 +
    20 * a ^ 2 / ((m : ℝ) ^ 10 * Real.pi * (m : ℝ) ^ 6) +
    4 * Real.pi * ((m : ℝ) ^ 6) ^ 4 / a ^ 2 + 20 * a / (Real.pi * (m : ℝ) ^ 6))
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hmain : C₀ * ((m : ℝ) ^ 10) ^ (s.re - 1) * ‖q‖ * D ≤ 1067 * C₀ * C₁ / m := by
    calc
      _ = C₀ * (((m : ℝ) ^ 10) ^ (s.re - 1) * ‖q‖) * D := by ring
      _ ≤ C₀ * (C₁ / Real.sqrt ((m : ℝ) ^ 10)) * D :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hnormle hC₀.le) hD
      _ = (C₀ * C₁) * ((1 / Real.sqrt ((m : ℝ) ^ 10)) * D) := by ring
      _ ≤ (C₀ * C₁) * (1067 / (m : ℝ)) := mul_le_mul_of_nonneg_left
        (spatial_profile_remainder_decay hm1 halo hahi) (mul_nonneg hC₀.le hC₁.le)
      _ = _ := by ring
  have hKs : 52 * ‖s - (1 / 2 : ℂ)‖ + 20 * ‖s - (1 / 2 : ℂ)‖ ^ 2 + 26 ≤ K := by
    dsimp only [K]
    gcongr
  have hshift : (52 * ‖s - (1 / 2 : ℂ)‖ + 20 * ‖s - (1 / 2 : ℂ)‖ ^ 2 + 26) / (2 * Real.pi * a) ≤ K / m :=
    (div_le_div_of_nonneg_right hKs (by positivity)).trans
      (div_le_div_of_nonneg_left hK hm0 (hmN.trans ht.1))
  exact hb.trans ((add_le_add hmain hshift).trans_eq (by ring))

end RHTower
