import GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.ArithmeticMellinReflection
import GaloisForLFunctions.HTGeometry.GammaVerticalRatioBound
import GaloisForLFunctions.HTGeometry.LpContinuousMultiplierNorm
import GaloisForLFunctions.RHTower.GaussComponentVerticalMagnitude

/-!
# Exact frequency order of Cauchy-averaged reflection

The actual core reflection multiplier has frequency order `1/2−2 Re s`.
Its Gamma quotient has an exact maximum in the bounded direction; both directions
are bounded exactly on the critical line.
-/

set_option autoImplicit false
noncomputable section
open Complex Set Filter MeasureTheory Topology
open scoped ComplexConjugate
open GaloisForLFunctions RenormalizedIntersectionTheory
open MayerScatteringCore MayerCauchyMellinSymbol

namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering

/-- The frequency-independent normalization in the core reflection multiplier. -/
def mayerCoreReflectionConstant (s : ℂ) : ℝ :=
  ‖Gammaℝ (2 * s) * Gamma (s + 1 / 2)‖ /
    ‖Gammaℝ (2 * (riemannMayerReflect s)) * Gamma ((riemannMayerReflect s) + 1 / 2)‖

private theorem gamma_ne_zero_of_re_pos {z : ℂ} (hz : 0 < z.re) : Gamma z ≠ 0 := by
  apply Complex.Gamma_ne_zero
  intro n hn
  have he := congrArg Complex.re hn
  simp only [Complex.neg_re, Complex.natCast_re] at he
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith only [hz, he, hn0]

/-- The normalizing constant is strictly positive throughout the open parameter strip. -/
theorem mayerCoreReflectionConstant_pos (s : ℂ) (hs0 : 0 < s.re) (hs1 : s.re < 1 / 2) :
    0 < mayerCoreReflectionConstant s := by
  have hn (q : ℂ) (hq : 0 < q.re) :
      0 < ‖Gammaℝ (2 * q) * Gamma (q + 1 / 2)‖ := by
    apply norm_pos_iff.mpr
    apply mul_ne_zero
    · exact Complex.Gammaℝ_ne_zero_of_re_pos (by simp; linarith only [hq])
    · exact gamma_ne_zero_of_re_pos (by simp; linarith only [hq])
  have href : 0 < (riemannMayerReflect s).re := by
    simp [riemannMayerReflect]
    linarith only [hs1]
  exact div_pos (hn s hs0) (hn (riemannMayerReflect s) href)

/-- Averaging changes reflection by an exact vertical Gamma quotient. Its two real offsets
are `1−Re s` and `Re s+1/2`; their difference is `1/2−2 Re s`. -/
theorem norm_mayerCoreReflectionFactor (s : ℂ) (hs0 : 0 < s.re) (hs1 : s.re < 1 / 2) (t : ℝ) :
    ‖mayerCoreReflectionFactor s t‖ = mayerCoreReflectionConstant s *
      (‖Gamma (((1 - s.re : ℝ) : ℂ) + ((s.im - t / 2 : ℝ) : ℂ) * I)‖ /
        ‖Gamma (((s.re + 1 / 2 : ℝ) : ℂ) + ((s.im - t / 2 : ℝ) : ℂ) * I)‖) := by
  have href : 0 < (riemannMayerReflect s).re := by
    simp [riemannMayerReflect]
    linarith only [hs1]
  have hden (q : ℂ) (hq : 0 < q.re) : Gammaℝ (2 * q) ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (by simp; linarith only [hq])
  have hhalf (q : ℂ) (hq : 0 < q.re) : Gamma (q + 1 / 2) ≠ 0 :=
    gamma_ne_zero_of_re_pos (by simp; linarith only [hq])
  have ht : Gamma (((t : ℂ) * I + 1) / 2) ≠ 0 := gamma_ne_zero_of_re_pos (by simp)
  have hmid (q : ℂ) (hq : 0 < q.re) : Gamma ((2 * q + 1 - (t : ℂ) * I) / 2) ≠ 0 :=
    gamma_ne_zero_of_re_pos (by simp; linarith only [hq])
  have hpi : (Real.pi : ℂ) ^ (1 / 2 : ℂ) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  have hoff (q : ℂ) : (2 * q + 1) / 2 = q + 1 / 2 := by ring
  have ha : (2 * s + 1 - (t : ℂ) * I) / 2 =
      (((s.re + 1 / 2 : ℝ) : ℂ) + ((s.im - t / 2 : ℝ) : ℂ) * I) := by
    apply Complex.ext <;> simp <;> ring
  have hb : (2 * (riemannMayerReflect s) + 1 - (t : ℂ) * I) / 2 =
      (((1 - s.re : ℝ) : ℂ) + ((s.im - t / 2 : ℝ) : ℂ) * I) := by
    simp only [riemannMayerReflect]
    apply Complex.ext <;> simp <;> ring
  rw [← ha, ← hb]
  simp only [mayerCoreReflectionFactor, mayerCoreMellinFactor, mayerCoreReflectionConstant,
    symbol, norm_div, norm_mul, Complex.norm_conj, hoff]
  field_simp [norm_ne_zero_iff.mpr (hden s hs0), norm_ne_zero_iff.mpr (hden (riemannMayerReflect s) href),
    norm_ne_zero_iff.mpr (hhalf s hs0), norm_ne_zero_iff.mpr (hhalf (riemannMayerReflect s) href),
    norm_ne_zero_iff.mpr ht, norm_ne_zero_iff.mpr (hmid s hs0),
    norm_ne_zero_iff.mpr (hmid (riemannMayerReflect s) href), norm_ne_zero_iff.mpr hpi]

/-- In the bounded direction, the exact multiplier maximum occurs at frequency `2 Im s`. -/
theorem mayerCoreReflectionFactor_sharp_bound (s : ℂ) (hs0 : 0 < s.re) (hs1 : s.re < 1 / 2)
    (hs : 1 / 4 ≤ s.re) (t : ℝ) :
    ‖mayerCoreReflectionFactor s t‖ ≤
      ‖mayerCoreReflectionFactor s (2 * s.im)‖ := by
  rw [norm_mayerCoreReflectionFactor s hs0 hs1, norm_mayerCoreReflectionFactor s hs0 hs1]
  have hb : 0 < 1 - s.re := by linarith only [hs1]
  have hab : 1 - s.re ≤ s.re + 1 / 2 := by linarith only [hs]
  have he : s.im - 2 * s.im / 2 = 0 := by ring
  rw [he]
  simp only [Complex.ofReal_zero, zero_mul, add_zero, Complex.Gamma_ofReal,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.Gamma_pos_of_pos hb),
    abs_of_pos (Real.Gamma_pos_of_pos (lt_of_lt_of_le hb hab))]
  exact mul_le_mul_of_nonneg_left (_root_.HTGeometry.norm_Gamma_div_le hb hab _)
    (mayerCoreReflectionConstant_pos s hs0 hs1).le


private theorem gamma_ratio_mul_rpow_tendsto_of_le {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    Tendsto (fun τ : ℝ =>
      (‖Gamma ((a : ℂ) + (τ : ℂ) * I)‖ / ‖Gamma ((b : ℂ) + (τ : ℂ) * I)‖) *
        τ ^ (b - a)) atTop (𝓝 1) := by
  have hh := _root_.RHTower.gamma_vertical_ratio_log_tendsto ha.le (sub_nonneg.mpr hab)
  rw [show a + (b - a) = b by ring] at hh
  have he : Tendsto (fun τ : ℝ => Real.exp
      (Real.log ‖Gamma ((a : ℂ) + (τ : ℂ) * I)‖ -
        Real.log ‖Gamma ((b : ℂ) + (τ : ℂ) * I)‖ + (b - a) * Real.log τ)) atTop (𝓝 1) := by
    simpa only [Real.exp_zero, Function.comp_def] using Real.continuous_exp.continuousAt.tendsto.comp hh
  refine he.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with τ hτ
  have hGa : 0 < ‖Gamma ((a : ℂ) + (τ : ℂ) * I)‖ :=
    norm_pos_iff.mpr (gamma_ne_zero_of_re_pos (by simpa using ha))
  have hGb : 0 < ‖Gamma ((b : ℂ) + (τ : ℂ) * I)‖ :=
    norm_pos_iff.mpr (gamma_ne_zero_of_re_pos (by simpa using lt_of_lt_of_le ha hab))
  rw [Real.exp_add, Real.exp_sub, Real.exp_log hGa, Real.exp_log hGb,
    Real.rpow_def_of_pos hτ, mul_comm (b - a)]

private theorem gamma_ratio_mul_rpow_tendsto {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun τ : ℝ =>
      (‖Gamma ((a : ℂ) + (τ : ℂ) * I)‖ / ‖Gamma ((b : ℂ) + (τ : ℂ) * I)‖) *
        τ ^ (b - a)) atTop (𝓝 1) := by
  by_cases hab : a ≤ b
  · exact gamma_ratio_mul_rpow_tendsto_of_le ha hab
  · have hh := (gamma_ratio_mul_rpow_tendsto_of_le hb (not_le.mp hab).le).inv₀
      (by norm_num : (1 : ℝ) ≠ 0)
    simp only [inv_one] at hh
    refine hh.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with τ hτ
    rw [mul_inv, inv_div, show b - a = -(a - b) by ring, Real.rpow_neg hτ.le]

private theorem gamma_ratio_tendsto_zero {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    Tendsto (fun τ : ℝ =>
      ‖Gamma ((a : ℂ) + (τ : ℂ) * I)‖ / ‖Gamma ((b : ℂ) + (τ : ℂ) * I)‖)
        atTop (𝓝 0) := by
  have hh := (gamma_ratio_mul_rpow_tendsto_of_le ha hab.le).mul
    (tendsto_rpow_neg_atTop (sub_pos.mpr hab))
  simp only [mul_zero] at hh
  refine hh.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with τ hτ
  rw [mul_assoc, ← Real.rpow_add hτ, add_neg_cancel, Real.rpow_zero, mul_one]

/-- The exact frequency order of the physical core reflection is `1/2−2 Re s`.
The normalization tends to the strictly positive explicit Gamma constant. -/
theorem mayerCoreReflectionFactor_frequency_order (s : ℂ) (hs0 : 0 < s.re) (hs1 : s.re < 1 / 2) :
    Tendsto (fun τ : ℝ =>
      ‖mayerCoreReflectionFactor s (2 * (s.im - τ))‖ * τ ^ (2 * s.re - 1 / 2))
      atTop (𝓝 (mayerCoreReflectionConstant s)) := by
  have ha : 0 < 1 - s.re := by linarith only [hs1]
  have hb : 0 < s.re + 1 / 2 := by linarith only [hs0]
  have hh := (gamma_ratio_mul_rpow_tendsto ha hb).const_mul (mayerCoreReflectionConstant s)
  simp only [mul_one] at hh
  refine hh.congr (fun τ => ?_)
  rw [norm_mayerCoreReflectionFactor s hs0 hs1,
    show s.im - 2 * (s.im - τ) / 2 = τ by ring,
    show (s.re + 1 / 2) - (1 - s.re) = 2 * s.re - 1 / 2 by ring]
  ring

/-- Cauchy-averaged reflection is bounded in frequency exactly on one side of the critical line. -/
theorem mayerCoreReflectionFactor_bounded_iff (s : ℂ) (hs0 : 0 < s.re) (hs1 : s.re < 1 / 2) :
    (∃ C : ℝ, ∀ t : ℝ, ‖mayerCoreReflectionFactor s t‖ ≤ C) ↔ 1 / 4 ≤ s.re := by
  constructor
  · rintro ⟨C, hC⟩
    by_contra hs
    have ha : 0 < s.re + 1 / 2 := by linarith only [hs0]
    have hab : s.re + 1 / 2 < 1 - s.re := by linarith only [not_le.mp hs]
    have hlim := (gamma_ratio_tendsto_zero ha hab).const_mul C
    simp only [mul_zero] at hlim
    have hi (τ : ℝ) : mayerCoreReflectionConstant s ≤ C *
        (‖Gamma (((s.re + 1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I)‖ /
          ‖Gamma (((1 - s.re : ℝ) : ℂ) + (τ : ℂ) * I)‖) := by
      have hc := hC (2 * (s.im - τ))
      rw [norm_mayerCoreReflectionFactor s hs0 hs1,
        show s.im - 2 * (s.im - τ) / 2 = τ by ring] at hc
      have hGa : ‖Gamma (((s.re + 1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I)‖ ≠ 0 :=
        norm_ne_zero_iff.mpr (gamma_ne_zero_of_re_pos (by simpa using ha))
      have hGb : ‖Gamma (((1 - s.re : ℝ) : ℂ) + (τ : ℂ) * I)‖ ≠ 0 :=
        norm_ne_zero_iff.mpr (gamma_ne_zero_of_re_pos (by simpa using ha.trans hab))
      have hcancel (A B : ℝ) (hA : A ≠ 0) (hB : B ≠ 0) :
          mayerCoreReflectionConstant s = (mayerCoreReflectionConstant s * (B / A)) * (A / B) := by
        field_simp [hA, hB]
      calc
        _ = (mayerCoreReflectionConstant s *
            (‖Gamma (((1 - s.re : ℝ) : ℂ) + (τ : ℂ) * I)‖ /
              ‖Gamma (((s.re + 1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I)‖)) *
            (‖Gamma (((s.re + 1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I)‖ /
              ‖Gamma (((1 - s.re : ℝ) : ℂ) + (τ : ℂ) * I)‖) := hcancel _ _ hGa hGb
        _ ≤ _ := mul_le_mul_of_nonneg_right hc (div_nonneg (norm_nonneg _) (norm_nonneg _))
    have hbad := ge_of_tendsto hlim (Filter.Eventually.of_forall hi)
    exact (not_le_of_gt (mayerCoreReflectionConstant_pos s hs0 hs1)) hbad
  · intro hs
    exact ⟨‖mayerCoreReflectionFactor s (2 * s.im)‖, mayerCoreReflectionFactor_sharp_bound s hs0 hs1 hs⟩

/-- Both spectral directions have bounded Cauchy reflection factors exactly at the critical line. -/
theorem mayerCoreReflectionFactor_both_bounded_iff (s : ℂ) (hs0 : 0 < s.re) (hs1 : s.re < 1 / 2) :
    ((∃ C : ℝ, ∀ t : ℝ, ‖mayerCoreReflectionFactor s t‖ ≤ C) ∧
      (∃ C : ℝ, ∀ t : ℝ, ‖mayerCoreReflectionFactor (riemannMayerReflect s) t‖ ≤ C)) ↔
      s.re = 1 / 4 := by
  have hr : (riemannMayerReflect s).re = 1 / 2 - s.re := by simp [riemannMayerReflect]
  have hr0 : 0 < (riemannMayerReflect s).re := by rw [hr]; linarith only [hs1]
  have hr1 : (riemannMayerReflect s).re < 1 / 2 := by rw [hr]; linarith only [hs0]
  rw [mayerCoreReflectionFactor_bounded_iff s hs0 hs1,
    mayerCoreReflectionFactor_bounded_iff (riemannMayerReflect s) hr0 hr1, hr]
  constructor
  · rintro ⟨h1, h2⟩; linarith only [h1, h2]
  · intro h; rw [h]; norm_num

/-- The fixed-Haar Mellin multiplier cannot be bounded throughout the full parameter strip. -/
theorem mayerCoreReflectionFactor_not_bounded_on_strip :
    ¬ (∀ s : ℂ, 0 < s.re → s.re < 1 / 2 →
      ∃ C : ℝ, ∀ t : ℝ, ‖mayerCoreReflectionFactor s t‖ ≤ C) := by
  intro h
  have hp := (mayerCoreReflectionFactor_bounded_iff ((1 / 8 : ℂ) + I)
    (by norm_num) (by norm_num)).mp (h ((1 / 8 : ℂ) + I) (by norm_num) (by norm_num))
  norm_num at hp



private theorem continuousAt_gamma_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    ContinuousAt Gamma z := by
  apply (Complex.differentiableAt_Gamma z ?_).continuousAt
  intro n hn
  have he := congrArg Complex.re hn
  simp only [Complex.neg_re, Complex.natCast_re] at he
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith only [hz, he, hn0]

/-- The imaginary-axis Cauchy multiplier is continuous throughout the source half-plane. -/
theorem continuous_mayerCoreMellinFactor (s : ℂ) (hs : 0 < s.re) :
    Continuous (mayerCoreMellinFactor s) := by
  have h1 : Continuous (fun t : ℝ => Gamma (((t : ℂ) * I + 1) / 2)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (continuousAt_gamma_of_re_pos (by simp : 0 < (((t : ℂ) * I + 1) / 2).re)).comp
      (f := fun t : ℝ => ((t : ℂ) * I + 1) / 2) (by fun_prop)
  have h2 : Continuous (fun t : ℝ => Gamma ((2 * s + 1 - (t : ℂ) * I) / 2)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (continuousAt_gamma_of_re_pos
      (by simp; linarith only [hs] : 0 < ((2 * s + 1 - (t : ℂ) * I) / 2).re)).comp
      (f := fun t : ℝ => (2 * s + 1 - (t : ℂ) * I) / 2) (by fun_prop)
  exact ((h1.mul h2).div_const _).div_const _

/-- Cauchy averaging loses no imaginary-axis frequency on the source half-plane. -/
theorem mayerCoreMellinFactor_ne_zero_of_re_pos (s : ℂ) (hs : 0 < s.re) (t : ℝ) :
    mayerCoreMellinFactor s t ≠ 0 := by
  have hw : 0 < (2 * s).re := by simp; linarith only [hs]
  exact div_ne_zero (symbol_ne_zero hw (by simp) (by simp; linarith only [hs]))
    (Complex.Gammaℝ_ne_zero_of_re_pos hw)

/-- The full Cauchy correction is continuous, so its pointwise bounds are genuine multiplier bounds. -/
theorem continuous_mayerCoreReflectionFactor (s : ℂ) (hs0 : 0 < s.re) (hs1 : s.re < 1 / 2) :
    Continuous (mayerCoreReflectionFactor s) := by
  have href : 0 < (riemannMayerReflect s).re := by
    simp [riemannMayerReflect]
    linarith only [hs1]
  exact (continuous_mayerCoreMellinFactor (riemannMayerReflect s) href).div
    (Complex.continuous_conj.comp (continuous_mayerCoreMellinFactor s hs0))
    (fun t => (map_ne_zero (starRingEnd ℂ)).mpr (mayerCoreMellinFactor_ne_zero_of_re_pos s hs0 t))

/-- The Cauchy reflection correction as a bounded operator on the full imaginary-axis `L²` space. -/
def mayerCoreReflectionMultiplier (s : ℂ) (hs0 : 0 < s.re) (hs1 : s.re < 1 / 2)
    (hs : 1 / 4 ≤ s.re) :
    Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  lpBoundedMulCLM (continuous_mayerCoreReflectionFactor s hs0 hs1).measurable (norm_nonneg _)
    (mayerCoreReflectionFactor_sharp_bound s hs0 hs1 hs)

/-- The bounded operator retains the literal Cauchy reflection multiplier. -/
theorem mayerCoreReflectionMultiplier_coeFn (s : ℂ) (hs0 : 0 < s.re) (hs1 : s.re < 1 / 2)
    (hs : 1 / 4 ≤ s.re) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    (mayerCoreReflectionMultiplier s hs0 hs1 hs f : ℝ → ℂ) =ᵐ[volume]
      fun t => mayerCoreReflectionFactor s t * f t :=
  lpBoundedMulCLM_coeFn (continuous_mayerCoreReflectionFactor s hs0 hs1).measurable (norm_nonneg _)
    (mayerCoreReflectionFactor_sharp_bound s hs0 hs1 hs) f

/-- The multiplier's operator norm is exactly its attained frequency maximum. -/
theorem norm_mayerCoreReflectionMultiplier (s : ℂ) (hs0 : 0 < s.re) (hs1 : s.re < 1 / 2)
    (hs : 1 / 4 ≤ s.re) :
    ‖mayerCoreReflectionMultiplier s hs0 hs1 hs‖ = ‖mayerCoreReflectionFactor s (2 * s.im)‖ := by
  apply le_antisymm
  · exact norm_lpBoundedMulCLM_le
      (continuous_mayerCoreReflectionFactor s hs0 hs1).measurable (norm_nonneg _)
      (mayerCoreReflectionFactor_sharp_bound s hs0 hs1 hs)
  · exact norm_symbol_le_of_ae_mul_continuous (continuous_mayerCoreReflectionFactor s hs0 hs1)
      (mayerCoreReflectionMultiplier_coeFn s hs0 hs1 hs) (2 * s.im)

/-- Existence of a bounded `L²` realization of the actual correction is equivalent to the sharp
half-strip condition. No assumed operator is used in the forward construction. -/
theorem mayerCoreReflection_bounded_multiplier_iff (s : ℂ) (hs0 : 0 < s.re) (hs1 : s.re < 1 / 2) :
    (∃ T : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ),
      ∀ f, (T f : ℝ → ℂ) =ᵐ[volume] fun t => mayerCoreReflectionFactor s t * f t) ↔
      1 / 4 ≤ s.re := by
  constructor
  · rintro ⟨T, hT⟩
    apply (mayerCoreReflectionFactor_bounded_iff s hs0 hs1).mp
    exact ⟨‖T‖, norm_symbol_le_of_ae_mul_continuous
      (continuous_mayerCoreReflectionFactor s hs0 hs1) hT⟩
  · intro hs
    exact ⟨mayerCoreReflectionMultiplier s hs0 hs1 hs, mayerCoreReflectionMultiplier_coeFn s hs0 hs1 hs⟩

/-- No bounded multiplication realization exists at every parameter in the full strip. -/
theorem mayerCoreReflection_no_bounded_multiplier_family :
    ¬ (∀ s : ℂ, 0 < s.re → s.re < 1 / 2 →
      ∃ T : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ),
        ∀ f, (T f : ℝ → ℂ) =ᵐ[volume] fun t => mayerCoreReflectionFactor s t * f t) := by
  intro h
  apply mayerCoreReflectionFactor_not_bounded_on_strip
  intro s hs0 hs1
  exact (mayerCoreReflectionFactor_bounded_iff s hs0 hs1).mpr
    ((mayerCoreReflection_bounded_multiplier_iff s hs0 hs1).mp (h s hs0 hs1))


#print axioms norm_mayerCoreReflectionFactor
#print axioms mayerCoreReflectionFactor_sharp_bound
#print axioms mayerCoreReflectionFactor_frequency_order
#print axioms mayerCoreReflectionFactor_bounded_iff
#print axioms mayerCoreReflectionFactor_both_bounded_iff
#print axioms mayerCoreReflectionFactor_not_bounded_on_strip
#print axioms continuous_mayerCoreReflectionFactor
#print axioms norm_mayerCoreReflectionMultiplier
#print axioms mayerCoreReflection_bounded_multiplier_iff
#print axioms mayerCoreReflection_no_bounded_multiplier_family

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering
