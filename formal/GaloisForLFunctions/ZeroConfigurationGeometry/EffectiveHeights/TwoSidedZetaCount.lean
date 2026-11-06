import GaloisForLFunctions.ZeroConfigurationGeometry.EffectiveHeights.LocalZetaCount
import GaloisForLFunctions.RHTower.LittlewoodShortWindowZeroCount
import GaloisForLFunctions.RHTower.XiWardCriticalBudgetProbe
import GaloisForLFunctions.RHTower.XiOrderedPositiveZeros

/-!
# The explicit two-sided zero count

Between good heights the zero count is the integral of the archimedean density `μ`, up to the explicit
error `100 (log T₁ + log T₂) + 1`. The digamma asymptotics bound `μ` from both sides, so `N(a,b)` has a
lower bound as well as an upper bound, with absolute constants. There is no zero below height `5`, so the
global count is explicit too.
-/

open Complex MeasureTheory Set
open RHTower Zeta23 Zeta23.RvM

noncomputable section
namespace GaloisForLFunctions.ZeroConfigurationGeometry

/-- **The density of the Γ-side from below.** `μ(t) ≥ (log(t/2π) − 6/t)/2π` for `t ≥ 4`. -/
theorem mu_ge {τ : ℝ} (hτ : 4 ≤ τ) :
    (Real.log (τ / (2 * Real.pi)) - 6 / τ) / (2 * Real.pi) ≤ mu τ := by
  have hτ0 : 0 < τ := by linarith only [hτ]
  obtain ⟨z, hz⟩ : ∃ z : ℂ, z = linePt τ / 2 := ⟨_, rfl⟩
  have hzre : 0 < z.re := by
    rw [hz, Complex.div_ofNat_re, linePt_re]
    norm_num
  have hnorm_ge : τ / 2 ≤ ‖z‖ := by
    have h := Complex.abs_im_le_norm z
    rw [hz, Complex.div_ofNat_im, linePt_im, abs_div, abs_two, abs_of_pos hτ0] at h
    rw [hz]
    exact h
  have hz2 : 2 ≤ ‖z‖ := by linarith only [hnorm_ge, hτ]
  have hst := GaloisForLFunctions.HTGeometry.norm_digamma_sub_log_le_of_re_pos hzre hz2
  have hdig : Real.log ‖z‖ - 3 / ‖z‖ ≤ (Complex.digamma z).re := by
    have h1 := Complex.abs_re_le_norm (Complex.digamma z - Complex.log z)
    rw [Complex.sub_re, Complex.log_re] at h1
    have h2 := (abs_le.mp (h1.trans hst)).1
    linarith only [h2]
  have hlog : Real.log (τ / 2) ≤ Real.log ‖z‖ := Real.log_le_log (by positivity) hnorm_ge
  have hinv : 3 / ‖z‖ ≤ 6 / τ := by
    rw [div_le_div_iff₀ (by linarith only [hz2]) hτ0]
    linarith only [hnorm_ge]
  have hsplit : Real.log (τ / (2 * Real.pi)) = Real.log (τ / 2) - Real.log Real.pi := by
    rw [show τ / (2 * Real.pi) = (τ / 2) / Real.pi by ring,
      Real.log_div (by positivity) Real.pi_ne_zero]
  have e : linePt τ / 2 = 1 / 4 + Complex.I * τ / 2 := by
    rw [linePt]; push_cast; ring
  unfold mu
  rw [← e, ← hz]
  have hπ : 0 < 2 * Real.pi := by positivity
  rw [div_le_iff₀ hπ]
  have e2 : (1 / (2 * Real.pi) * (Complex.digamma z).re - Real.log Real.pi / (2 * Real.pi)) *
      (2 * Real.pi) = (Complex.digamma z).re - Real.log Real.pi := by
    field_simp
  rw [e2]
  linarith only [hdig, hlog, hinv, hsplit]

/-- **The contour identity with explicit error.** Between good heights the count is the integral of the
density, up to the horizontal Backlund terms and the argument of `ζ` on the line `Re s = 2`. -/
theorem abs_ncount_sub_integral_mu_le {T₁ T₂ : ℝ} (hT₁ : 4 ≤ T₁) (h12 : T₁ < T₂)
    (hg1 : GoodHeight T₁) (hg2 : GoodHeight T₂) :
    |(Ncount T₁ T₂ : ℝ) - ∫ t in T₁..T₂, mu t| ≤ 100 * (Real.log T₁ + Real.log T₂) + 1 := by
  have h1 : 1 ≤ T₁ := by linarith only [hT₁]
  have hN := N_eq_halfContour_completedZeta h1 h12 hg1 hg2
  have hsplit := halfContour_completedZeta_split h1 h12 hg1 hg2
  have hgam := gamma_side (T₁ := T₁) (T₂ := T₂) (by linarith only [hT₁])
    (by linarith only [hT₁, h12])
  have h5 : (Ncount T₁ T₂ : ℝ) =
      (1 / Real.pi) * (halfContour (logDeriv riemannZeta) T₁ T₂).im + ∫ t in T₁..T₂, mu t := by
    rw [hN, hsplit, Complex.add_im, mul_add, hgam]
  have hbk1 := backlund_horizontal_explicit hT₁ hg1
  have hbk2 := backlund_horizontal_explicit (by linarith only [hT₁, h12] : 4 ≤ T₂) hg2
  have hvert := vertical_two T₁ T₂
  have hζ : |(halfContour (logDeriv riemannZeta) T₁ T₂).im| ≤
      100 * Real.log T₁ + Real.pi + 100 * Real.log T₂ := by
    unfold halfContour
    rw [Complex.sub_im, Complex.add_im]
    have hmulI : ((∫ t in T₁..T₂, logDeriv riemannZeta (2 + t * I)) * I).im =
        (∫ t in T₁..T₂, logDeriv riemannZeta (2 + t * I) * I).im :=
      congrArg Complex.im (intervalIntegral.integral_mul_const (μ := MeasureTheory.volume) I
        (fun t : ℝ => logDeriv riemannZeta (2 + t * I))).symm
    rw [hmulI]
    have t1 := abs_sub ((∫ σ in (1 / 2 : ℝ)..2, logDeriv riemannZeta (σ + T₁ * I)).im +
      (∫ t in T₁..T₂, logDeriv riemannZeta (2 + t * I) * I).im)
      (∫ σ in (1 / 2 : ℝ)..2, logDeriv riemannZeta (σ + T₂ * I)).im
    have t2 := abs_add_le (∫ σ in (1 / 2 : ℝ)..2, logDeriv riemannZeta (σ + T₁ * I)).im
      (∫ t in T₁..T₂, logDeriv riemannZeta (2 + t * I) * I).im
    linarith only [t1, t2, hbk1, hbk2, hvert]
  have hlog₁ : 0 ≤ Real.log T₁ := Real.log_nonneg h1
  have hlog₂ : 0 ≤ Real.log T₂ := Real.log_nonneg (by linarith only [h1, h12])
  have hπ1 : 1 ≤ Real.pi := by linarith only [Real.pi_gt_three]
  have hπ0 : 0 < Real.pi := Real.pi_pos
  rw [h5, add_sub_cancel_right, abs_mul, abs_of_pos (by positivity : 0 < 1 / Real.pi), one_div,
    inv_mul_le_iff₀ hπ0]
  have hX : 0 ≤ 100 * (Real.log T₁ + Real.log T₂) := by positivity
  have hmul : 100 * (Real.log T₁ + Real.log T₂) ≤
      Real.pi * (100 * (Real.log T₁ + Real.log T₂)) := le_mul_of_one_le_left hX hπ1
  nlinarith only [hζ, hmul]

/-- The explicit lower count between good heights. -/
theorem ncount_ge_of_goodHeight {T₁ T₂ : ℝ} (hT₁ : 4 ≤ T₁) (h12 : T₁ < T₂)
    (hg1 : GoodHeight T₁) (hg2 : GoodHeight T₂) :
    (T₂ - T₁) * ((Real.log (T₁ / (2 * Real.pi)) - 6 / T₁) / (2 * Real.pi)) -
        100 * (Real.log T₁ + Real.log T₂) - 1 ≤ (Ncount T₁ T₂ : ℝ) := by
  have hT0 : 0 < T₁ := by linarith only [hT₁]
  have hmain := (abs_le.mp (abs_ncount_sub_integral_mu_le hT₁ h12 hg1 hg2)).1
  have hB0 : ∀ τ ∈ Icc T₁ T₂, (Real.log (T₁ / (2 * Real.pi)) - 6 / T₁) / (2 * Real.pi) ≤ mu τ := by
    intro τ hτ
    have hτ4 : 4 ≤ τ := by linarith only [hT₁, hτ.1]
    refine le_trans ?_ (mu_ge hτ4)
    have hpos : 0 < 2 * Real.pi := by positivity
    apply div_le_div_of_nonneg_right _ hpos.le
    have h1' : Real.log (T₁ / (2 * Real.pi)) ≤ Real.log (τ / (2 * Real.pi)) :=
      Real.log_le_log (by positivity) (div_le_div_of_nonneg_right hτ.1 hpos.le)
    have h2' : 6 / τ ≤ 6 / T₁ := div_le_div_of_nonneg_left (by norm_num) hT0 hτ.1
    linarith only [h1', h2']
  have hint := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) h12.le
    intervalIntegrable_const ((mu_continuous gammaFacts).intervalIntegrable _ _) hB0
  rw [intervalIntegral.integral_const, smul_eq_mul] at hint
  linarith only [hmain, hint]

/-- The explicit upper count between good heights. -/
theorem ncount_le_of_goodHeight_four {T₁ T₂ : ℝ} (hT₁ : 4 ≤ T₁) (h12 : T₁ < T₂)
    (hg1 : GoodHeight T₁) (hg2 : GoodHeight T₂) :
    (Ncount T₁ T₂ : ℝ) ≤ (T₂ - T₁) * ((Real.log ((T₂ + 1) / (2 * Real.pi)) + 6 / T₁) /
      (2 * Real.pi)) + 100 * (Real.log T₁ + Real.log T₂) + 1 := by
  have hT0 : 0 < T₁ := by linarith only [hT₁]
  have hmain := (abs_le.mp (abs_ncount_sub_integral_mu_le hT₁ h12 hg1 hg2)).2
  have hB0 : ∀ τ ∈ Icc T₁ T₂, mu τ ≤ (Real.log ((T₂ + 1) / (2 * Real.pi)) + 6 / T₁) /
      (2 * Real.pi) := by
    intro τ hτ
    have hτ4 : 4 ≤ τ := by linarith only [hT₁, hτ.1]
    refine (mu_le hτ4).trans ?_
    have hpos : 0 < 2 * Real.pi := by positivity
    apply div_le_div_of_nonneg_right _ hpos.le
    have h1' : Real.log ((τ + 1) / (2 * Real.pi)) ≤ Real.log ((T₂ + 1) / (2 * Real.pi)) :=
      Real.log_le_log (by positivity)
        (div_le_div_of_nonneg_right (by linarith only [hτ.2]) hpos.le)
    have h2' : 6 / τ ≤ 6 / T₁ := div_le_div_of_nonneg_left (by norm_num) hT0 hτ.1
    linarith only [h1', h2']
  have hint := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) h12.le
    ((mu_continuous gammaFacts).intervalIntegrable _ _) intervalIntegrable_const hB0
  rw [intervalIntegral.integral_const, smul_eq_mul] at hint
  linarith only [hmain, hint]

/-- The difference of the counting function is the window count. -/
theorem xiZeroCount_sub_eq_ncount {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (xiZeroCount b : ℝ) - xiZeroCount a = (Ncount a b : ℝ) := by
  have h := Littlewood.xiZeroCount_sub_eq ha hab
  have h2 : zetaZeroConfig.N a b = Ncount a b := zetaZeros_N zetaSeam a b
  rw [h2] at h
  exact_mod_cast h

/-- The counting function is monotone on the nonnegative half-line. -/
theorem xiZeroCount_mono_real {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (xiZeroCount a : ℝ) ≤ xiZeroCount b := by
  have h := xiZeroCount_sub_eq_ncount ha hab
  have h0 : (0 : ℝ) ≤ (Ncount a b : ℝ) := Nat.cast_nonneg _
  linarith only [h, h0]

/-- **The explicit upper window count, with multiplicity.** -/
theorem xiZeroCount_window_le {a b : ℝ} (ha : 10 ≤ a) (hab : a ≤ b) :
    (xiZeroCount b : ℝ) - xiZeroCount a ≤
      (b - a + 3) * ((Real.log ((b + 2) / (2 * Real.pi)) + 6 / (a - 2)) / (2 * Real.pi)) +
        200 * Real.log (b + 2) + 1 := by
  obtain ⟨T₁, hT₁mem, hg1⟩ := exists_goodHeight (a - 2)
  obtain ⟨T₂, hT₂mem, hg2⟩ := exists_goodHeight b
  have hT₁a : a - 2 ≤ T₁ := hT₁mem.1
  have hT₁b : T₁ ≤ a - 1 := by linarith only [hT₁mem.2]
  have hT₂a : b ≤ T₂ := hT₂mem.1
  have hT₂b : T₂ ≤ b + 1 := hT₂mem.2
  have h8 : 4 ≤ T₁ := by linarith only [ha, hT₁a]
  have h12 : T₁ < T₂ := by linarith only [hT₁b, hT₂a, hab]
  have hcount := ncount_le_of_goodHeight_four h8 h12 hg1 hg2
  have hT₁0 : 0 ≤ T₁ := by linarith only [h8]
  have hmono₁ := xiZeroCount_mono_real hT₁0 (by linarith only [hT₁b] : T₁ ≤ a)
  have hmono₂ := xiZeroCount_mono_real (by linarith only [ha, hab] : 0 ≤ b) hT₂a
  have hNeq := xiZeroCount_sub_eq_ncount hT₁0 h12.le
  have hpos : 0 < 2 * Real.pi := by positivity
  have hlogpos : 0 ≤ Real.log ((T₂ + 1) / (2 * Real.pi)) :=
    Real.log_nonneg ((one_le_div hpos).mpr (by linarith only [Real.pi_lt_four, ha, hab, hT₂a]))
  have hD1 : (Real.log ((T₂ + 1) / (2 * Real.pi)) + 6 / T₁) / (2 * Real.pi) ≤
      (Real.log ((b + 2) / (2 * Real.pi)) + 6 / (a - 2)) / (2 * Real.pi) := by
    apply div_le_div_of_nonneg_right _ hpos.le
    have h1' : Real.log ((T₂ + 1) / (2 * Real.pi)) ≤ Real.log ((b + 2) / (2 * Real.pi)) :=
      Real.log_le_log (div_pos (by linarith only [h8, h12]) hpos)
        (div_le_div_of_nonneg_right (by linarith only [hT₂b]) hpos.le)
    have h2' : 6 / T₁ ≤ 6 / (a - 2) :=
      div_le_div_of_nonneg_left (by norm_num) (by linarith only [ha]) hT₁a
    linarith only [h1', h2']
  have hD0 : 0 ≤ (Real.log ((T₂ + 1) / (2 * Real.pi)) + 6 / T₁) / (2 * Real.pi) := by
    have : 0 < 6 / T₁ := div_pos (by norm_num) (by linarith only [h8])
    exact div_nonneg (by linarith only [this, hlogpos]) hpos.le
  have hlen : T₂ - T₁ ≤ b - a + 3 := by linarith only [hT₁a, hT₂b]
  have hprod := mul_le_mul hlen hD1 hD0 (by linarith only [hab] : 0 ≤ b - a + 3)
  have hl1 : Real.log T₁ ≤ Real.log (b + 2) :=
    Real.log_le_log (by linarith only [h8]) (by linarith only [hT₁b, hab])
  have hl2 : Real.log T₂ ≤ Real.log (b + 2) :=
    Real.log_le_log (by linarith only [h8, h12]) (by linarith only [hT₂b])
  linarith only [hcount, hmono₁, hmono₂, hNeq, hprod, hl1, hl2]

/-- **The explicit lower window count, with multiplicity.** -/
theorem le_xiZeroCount_window {a b : ℝ} (ha : 20 ≤ a) (hab : a + 3 ≤ b) :
    (b - a - 2) * ((Real.log (a / (2 * Real.pi)) - 6 / a) / (2 * Real.pi)) -
        200 * Real.log b - 1 ≤ (xiZeroCount b : ℝ) - xiZeroCount a := by
  obtain ⟨T₁, hT₁mem, hg1⟩ := exists_goodHeight a
  obtain ⟨T₂, hT₂mem, hg2⟩ := exists_goodHeight (b - 1)
  have hT₁a : a ≤ T₁ := hT₁mem.1
  have hT₁b : T₁ ≤ a + 1 := hT₁mem.2
  have hT₂a : b - 1 ≤ T₂ := hT₂mem.1
  have hT₂b : T₂ ≤ b := by linarith only [hT₂mem.2]
  have h4 : 4 ≤ T₁ := by linarith only [ha, hT₁a]
  have h12 : T₁ < T₂ := by linarith only [hT₁b, hT₂a, hab]
  have hcount := ncount_ge_of_goodHeight h4 h12 hg1 hg2
  have ha0 : 0 < a := by linarith only [ha]
  have hT₁0 : 0 < T₁ := by linarith only [h4]
  have hmono₁ := xiZeroCount_mono_real ha0.le hT₁a
  have hmono₂ := xiZeroCount_mono_real (by linarith only [h4, h12] : 0 ≤ T₂) hT₂b
  have hNeq := xiZeroCount_sub_eq_ncount hT₁0.le h12.le
  have hpos : 0 < 2 * Real.pi := by positivity
  have hD1 : (Real.log (a / (2 * Real.pi)) - 6 / a) / (2 * Real.pi) ≤
      (Real.log (T₁ / (2 * Real.pi)) - 6 / T₁) / (2 * Real.pi) := by
    apply div_le_div_of_nonneg_right _ hpos.le
    have h1' : Real.log (a / (2 * Real.pi)) ≤ Real.log (T₁ / (2 * Real.pi)) :=
      Real.log_le_log (by positivity) (div_le_div_of_nonneg_right hT₁a hpos.le)
    have h2' : 6 / T₁ ≤ 6 / a := div_le_div_of_nonneg_left (by norm_num) ha0 hT₁a
    linarith only [h1', h2']
  have hD0 : 0 ≤ (Real.log (a / (2 * Real.pi)) - 6 / a) / (2 * Real.pi) := by
    apply div_nonneg _ hpos.le
    have h3 : 1 ≤ Real.log (a / (2 * Real.pi)) := by
      rw [Real.le_log_iff_exp_le (by positivity), le_div_iff₀ hpos]
      have he := Real.exp_one_lt_d9
      have hpi := Real.pi_lt_d2
      nlinarith only [he, hpi, ha, Real.pi_pos]
    have h6 : 6 / a ≤ 1 := by
      rw [div_le_one ha0]
      linarith only [ha]
    linarith only [h3, h6]
  have hlen : b - a - 2 ≤ T₂ - T₁ := by linarith only [hT₁b, hT₂a]
  have hprod := mul_le_mul hlen hD1 hD0 (by linarith only [h12] : 0 ≤ T₂ - T₁)
  have hb0 : 0 < b := by linarith only [ha0, hab]
  have hl1 : Real.log T₁ ≤ Real.log b :=
    Real.log_le_log hT₁0 (by linarith only [hT₁b, hab])
  have hl2 : Real.log T₂ ≤ Real.log b :=
    Real.log_le_log (by linarith only [h4, h12]) hT₂b
  linarith only [hcount, hmono₁, hmono₂, hNeq, hprod, hl1, hl2]

/-- No zero of `ζ` has height in `(0, 5]`, so the counting function vanishes there. -/
theorem xiZeroCount_eq_zero_of_le_five {T : ℝ} (hT0 : 0 ≤ T) (hT : T ≤ 5) :
    (xiZeroCount T : ℝ) = 0 := by
  have hempty : zerosIn 0 T = ∅ := by
    ext ρ
    simp only [mem_empty_iff_false, iff_false]
    rintro ⟨hρ, him0, himT⟩
    have him : ρ.im ^ 2 ≤ 32 := by nlinarith only [him0, himT, hT]
    have hne : ρ ≠ 1 := by
      intro h
      rw [h, Complex.one_im] at him0
      exact lt_irrefl _ him0
    exact riemannZeta_ne_zero_of_im_sq_le hne hρ.2.1 him hρ.1
  have hN : Ncount 0 T = 0 := by
    rw [Ncount, hempty, finsum_mem_empty]
  have h := xiZeroCount_sub_eq_ncount (le_refl (0 : ℝ)) hT0
  rw [hN, xiZeroCount_zero] at h
  simpa only [Int.cast_zero, sub_zero, Nat.cast_zero] using h

/-- **The explicit global count.** -/
theorem xiZeroCount_le_explicit {T : ℝ} (hT : 10 ≤ T) :
    (xiZeroCount T : ℝ) ≤
      T * ((Real.log ((T + 2) / (2 * Real.pi)) + 6 / 4) / (2 * Real.pi)) +
        200 * Real.log (T + 2) + 1 := by
  obtain ⟨T₁, hT₁mem, hg1⟩ := exists_goodHeight 4
  obtain ⟨T₂, hT₂mem, hg2⟩ := exists_goodHeight T
  have hT₁a : 4 ≤ T₁ := hT₁mem.1
  have hT₁b : T₁ ≤ 5 := by linarith only [hT₁mem.2]
  have hT₂a : T ≤ T₂ := hT₂mem.1
  have hT₂b : T₂ ≤ T + 1 := hT₂mem.2
  have h12 : T₁ < T₂ := by linarith only [hT₁b, hT₂a, hT]
  have hT₁0 : 0 < T₁ := by linarith only [hT₁a]
  have hcount := ncount_le_of_goodHeight_four hT₁a h12 hg1 hg2
  have hzero := xiZeroCount_eq_zero_of_le_five hT₁0.le hT₁b
  have hmono := xiZeroCount_mono_real (by linarith only [hT] : 0 ≤ T) hT₂a
  have hNeq := xiZeroCount_sub_eq_ncount hT₁0.le h12.le
  have hpos : 0 < 2 * Real.pi := by positivity
  have hlogpos : 0 ≤ Real.log ((T₂ + 1) / (2 * Real.pi)) :=
    Real.log_nonneg ((one_le_div hpos).mpr (by linarith only [Real.pi_lt_four, hT, hT₂a]))
  have hD1 : (Real.log ((T₂ + 1) / (2 * Real.pi)) + 6 / T₁) / (2 * Real.pi) ≤
      (Real.log ((T + 2) / (2 * Real.pi)) + 6 / 4) / (2 * Real.pi) := by
    apply div_le_div_of_nonneg_right _ hpos.le
    have h1' : Real.log ((T₂ + 1) / (2 * Real.pi)) ≤ Real.log ((T + 2) / (2 * Real.pi)) :=
      Real.log_le_log (div_pos (by linarith only [hT₁a, h12]) hpos)
        (div_le_div_of_nonneg_right (by linarith only [hT₂b]) hpos.le)
    have h2' : 6 / T₁ ≤ 6 / 4 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hT₁a
    linarith only [h1', h2']
  have hD0 : 0 ≤ (Real.log ((T₂ + 1) / (2 * Real.pi)) + 6 / T₁) / (2 * Real.pi) := by
    have : 0 < 6 / T₁ := div_pos (by norm_num) hT₁0
    exact div_nonneg (by linarith only [this, hlogpos]) hpos.le
  have hlen : T₂ - T₁ ≤ T := by linarith only [hT₁a, hT₂b]
  have hprod := mul_le_mul hlen hD1 hD0 (by linarith only [hT] : 0 ≤ T)
  have hl1 : Real.log T₁ ≤ Real.log (T + 2) :=
    Real.log_le_log hT₁0 (by linarith only [hT₁b, hT])
  have hl2 : Real.log T₂ ≤ Real.log (T + 2) :=
    Real.log_le_log (by linarith only [hT₁a, h12]) (by linarith only [hT₂b])
  linarith only [hcount, hzero, hmono, hNeq, hprod, hl1, hl2]

end GaloisForLFunctions.ZeroConfigurationGeometry
