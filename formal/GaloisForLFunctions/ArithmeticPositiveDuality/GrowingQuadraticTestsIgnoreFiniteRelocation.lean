import GaloisForLFunctions.ArithmeticPositiveDuality.FiniteZeroRelocationPreservesTheMeanSpectrum
import GaloisForLFunctions.ArithmeticPositiveDuality.TheVerticalTraceOfZeroRelocation
import GaloisForLFunctions.ArithmeticPositiveDuality.NormalizedRelocationHasASignedDensity
import GaloisForLFunctions.RHTower.ZetaConvexityBound
import Mathlib.Algebra.Order.Chebyshev

/-!
# Growing quadratic tests ignore finite symmetric relocation

Symmetry cancels the cubic terms of the relocation numerator and denominator.
The multiplier differs from one by `O(t⁻²)`. Consequently quadratic means on
fixed lines right of the critical line survive tests whose squared modulus is
bounded by `o(T²)` on `[T,2T]`. Uniform convexity extends this stability to
moving lines near the critical line, for tests whose term count times coefficient
energy is `o(T)`. Actual critical-line donors give a residue-preserving model
with an off-line zero and the same short tested means.
-/

open Complex Filter Topology Set MeasureTheory

noncomputable section
namespace GaloisForLFunctions.ArithmeticPositiveDuality

/-- Symmetric relocation changes squared moduli by at most `C/t²` eventually. -/
theorem eventually_scaled_zeroRelocation_normSq_sub_one_le (ρ : ℂ) (γ₁ γ₂ : ℝ)
    (σ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t : ℝ in atTop,
      t^2 * |‖zeroRelocationFactor ρ γ₁ γ₂ ((σ : ℂ) + (t : ℂ)*I)‖^2 - 1| ≤ C := by
  let A : ℂ := -(relocationQuadraticCoefficient ρ γ₁ γ₂ : ℂ)
  have hscaled := (tendsto_quadratic_vertical_relocation_error ρ γ₁ γ₂ σ).norm
  have hsmall := (tendsto_zeroRelocationFactor_vertical_atTop ρ γ₁ γ₂ σ).norm
  refine ⟨3 * (‖A‖ + 1), by positivity, ?_⟩
  filter_upwards [hscaled.eventually_lt_const (lt_add_one ‖A‖),
    hsmall.eventually_lt_const (show ‖(1 : ℂ)‖ < 2 by norm_num)] with t hbound hm
  let m := zeroRelocationFactor ρ γ₁ γ₂ ((σ : ℂ) + (t : ℂ)*I)
  have hb : t^2 * ‖m - 1‖ ≤ ‖A‖ + 1 := by
    simpa only [norm_mul, norm_pow, norm_real, Real.norm_eq_abs, sq_abs] using hbound.le
  have hd : |‖m‖ - 1| ≤ ‖m - 1‖ := by
    apply abs_le.mpr
    have h₁ := norm_sub_norm_le m (1 : ℂ)
    have h₂ := norm_sub_norm_le (1 : ℂ) m
    rw [norm_one] at h₁ h₂
    rw [norm_sub_rev] at h₂
    exact ⟨by linarith only [h₂], h₁⟩
  have hs : |‖m‖^2 - 1| ≤ 3 * ‖m - 1‖ := by
    rw [show ‖m‖^2 - 1 = (‖m‖ - 1) * (‖m‖ + 1) by ring,
      abs_mul, abs_of_nonneg (by positivity : 0 ≤ ‖m‖ + 1)]
    have h := mul_le_mul hd (show ‖m‖ + 1 ≤ 3 by linarith only [hm])
      (by positivity : 0 ≤ ‖m‖ + 1) (norm_nonneg (m - 1))
    simpa only [mul_comm ‖m - 1‖ 3] using h
  have h := mul_le_mul_of_nonneg_left hs (sq_nonneg t)
  change t^2 * |‖m‖^2 - 1| ≤ _
  nlinarith only [h, hb]

private theorem tendsto_moving_weighted_squareMean_sub
    {F m : ℝ → ℂ} (hF : Continuous F) (hm : Continuous m)
    {C D : ℝ} (hD : 0 ≤ D)
    (hmean : ∀ᶠ T : ℝ in atTop, (∫ t in T..2*T, ‖F t‖^2) / T ≤ C)
    (hdec : ∀ᶠ t : ℝ in atTop, t^2 * |‖m t‖^2 - 1| ≤ D)
    {W : ℝ → ℝ → ℝ} (hW : ∀ T, Continuous (W T)) (hW0 : ∀ T t, 0 ≤ W T t)
    {N : ℝ → ℝ} (hN0 : ∀ T, 0 ≤ N T)
    (hWN : ∀ T t, T ≤ t → t ≤ 2*T → W T t ≤ N T)
    (hN : Tendsto (fun T : ℝ => N T / T^2) atTop (𝓝 0)) :
    Tendsto (fun T : ℝ =>
      (∫ t in T..2*T, (‖F t * m t‖^2 - ‖F t‖^2) * W T t) / T)
      atTop (𝓝 0) := by
  obtain ⟨L, hL⟩ := eventually_atTop.mp hdec
  refine squeeze_zero_norm' (a := fun T => D*C*(N T/T^2)) ?_
    (by simpa only [mul_zero] using hN.const_mul (D*C))
  filter_upwards [eventually_ge_atTop (max L 1), hmean] with T hT hM
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one ((le_max_right _ _).trans hT)
  have hTL : L ≤ T := (le_max_left _ _).trans hT
  have hTT : T ≤ 2*T := by linarith only [hT0]
  have hT2 : 0 < T^2 := sq_pos_of_pos hT0
  have hNT : 0 ≤ N T := hN0 T
  have hpt (t : ℝ) (ht : t ∈ Icc T (2*T)) :
      |(‖F t * m t‖^2 - ‖F t‖^2) * W T t| ≤ (D*N T/T^2)*‖F t‖^2 := by
    have he : |‖m t‖^2 - 1| ≤ D/T^2 := by
      apply (le_div_iff₀ hT2).mpr
      have hpow := pow_le_pow_left₀ hT0.le ht.1 2
      have hmul := mul_le_mul_of_nonneg_right hpow (abs_nonneg (‖m t‖^2 - 1))
      calc |‖m t‖^2 - 1| * T^2 = T^2 * |‖m t‖^2 - 1| := by ring
        _ ≤ t^2 * |‖m t‖^2 - 1| := hmul
        _ ≤ D := hL t (hTL.trans ht.1)
    rw [norm_mul, mul_pow,
      show ‖F t‖^2 * ‖m t‖^2 - ‖F t‖^2 = ‖F t‖^2 * (‖m t‖^2 - 1) by ring,
      abs_mul, abs_mul, abs_of_nonneg (sq_nonneg _), abs_of_nonneg (hW0 T t)]
    calc ‖F t‖^2 * |‖m t‖^2 - 1| * W T t
        ≤ (‖F t‖^2 * (D/T^2)) * N T :=
          mul_le_mul (mul_le_mul_of_nonneg_left he (sq_nonneg _))
            (hWN T t ht.1 ht.2) (hW0 T t) (by positivity)
      _ = _ := by ring
  have hWc := hW T
  have hi : |∫ t in T..2*T, (‖F t * m t‖^2 - ‖F t‖^2) * W T t| ≤
      (D*N T/T^2) * ∫ t in T..2*T, ‖F t‖^2 := by
    calc
      _ ≤ ∫ t in T..2*T, |(‖F t * m t‖^2 - ‖F t‖^2) * W T t| :=
        intervalIntegral.abs_integral_le_integral_abs hTT
      _ ≤ ∫ t in T..2*T, (D*N T/T^2)*‖F t‖^2 :=
        intervalIntegral.integral_mono_on hTT
          ((by fun_prop : Continuous fun t => |(‖F t * m t‖^2 - ‖F t‖^2) * W T t|).intervalIntegrable _ _)
          ((by fun_prop : Continuous fun t => (D*N T/T^2)*‖F t‖^2).intervalIntegrable _ _)
          hpt
      _ = _ := intervalIntegral.integral_const_mul _ _
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hT0]
  calc
    _ ≤ ((D*N T/T^2) * ∫ t in T..2*T, ‖F t‖^2) / T :=
      div_le_div_of_nonneg_right hi hT0.le
    _ = (D*N T/T^2) * ((∫ t in T..2*T, ‖F t‖^2) / T) := by ring
    _ ≤ (D*N T/T^2)*C := mul_le_mul_of_nonneg_left hM (by positivity)
    _ = _ := by ring

private theorem eventually_zeta_window_squareMean_bounded {σ : ℝ}
    (hσ : 1/2 < σ) (hσ1 : σ ≠ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop,
      (∫ t in T..2*T, ‖riemannZeta ((σ : ℂ) + (t : ℂ)*I)‖^2) / T ≤ C := by
  obtain ⟨C, hC⟩ := eventually_zeta_squareMean_bounded hσ hσ1
  have htwice : Tendsto (fun T : ℝ => 2*T) atTop atTop :=
    tendsto_id.const_mul_atTop (by norm_num)
  refine ⟨2*(|C|+1), by positivity, ?_⟩
  filter_upwards [htwice.eventually hC, eventually_gt_atTop (0 : ℝ)] with T hM hT
  have hf := (RHTower.continuous_riemannZeta_vertical_line hσ1).norm.pow 2
  have hs := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hf.intervalIntegrable 0 T) (hf.intervalIntegrable T (2*T))
  dsimp only [Pi.pow_apply] at hs
  have hp : 0 ≤ ∫ t in (0 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + (t : ℂ)*I)‖^2 :=
    intervalIntegral.integral_nonneg hT.le fun _ _ => sq_nonneg _
  have hM' := (div_le_iff₀ (show 0 < 2*T by positivity)).mp hM
  apply (div_le_iff₀ hT).mpr
  have hCT := mul_le_mul_of_nonneg_right (le_abs_self C) hT.le
  nlinarith only [hs, hp, hM', hCT, hT]

/-- On a fixed line right of `1/2`, relocation preserves every quadratic mean with
nonnegative continuous weights bounded by `o(T²)` on `[T,2T]`. Uniform convexity extends this stability to
moving lines near the critical line, for tests whose term count times coefficient
energy is `o(T)`. Actual critical-line donors give a residue-preserving model
with an off-line zero and the same short tested means. -/
theorem relocation_preserves_growing_weighted_mean (ρ : ℂ) (γ₁ γ₂ : ℝ)
    {σ : ℝ} (hσ : 1/2 < σ) (hσ1 : σ ≠ 1)
    {W : ℝ → ℝ → ℝ} (hW : ∀ T, Continuous (W T)) (hW0 : ∀ T t, 0 ≤ W T t)
    {N : ℝ → ℝ} (hN0 : ∀ T, 0 ≤ N T)
    (hWN : ∀ T t, T ≤ t → t ≤ 2*T → W T t ≤ N T)
    (hN : Tendsto (fun T : ℝ => N T / T^2) atTop (𝓝 0)) :
    Tendsto (fun T : ℝ => (∫ t in T..2*T,
      (‖relocatedZeta ρ γ₁ γ₂ ((σ : ℂ) + (t : ℂ)*I)‖^2 -
        ‖riemannZeta ((σ : ℂ) + (t : ℂ)*I)‖^2) * W T t) / T) atTop (𝓝 0) := by
  obtain ⟨C, _, hmean⟩ := eventually_zeta_window_squareMean_bounded hσ hσ1
  obtain ⟨D, hD, hdec⟩ := eventually_scaled_zeroRelocation_normSq_sub_one_le ρ γ₁ γ₂ σ
  exact tendsto_moving_weighted_squareMean_sub
    (RHTower.continuous_riemannZeta_vertical_line hσ1)
    (continuous_zeroRelocationFactor_vertical ρ γ₁ γ₂ hσ.ne') hD.le hmean hdec
    hW hW0 hN0 hWN hN

private theorem norm_sq_trig_test_le_energy {n : ℕ} (a : Fin n → ℂ) (ω : Fin n → ℝ)
    (t : ℝ) :
    ‖∑ k, a k * Complex.exp ((ω k : ℂ)*I*(t : ℂ))‖^2 ≤ (n : ℝ)*∑ k, ‖a k‖^2 := by
  have hnorm : ‖∑ k, a k * Complex.exp ((ω k : ℂ)*I*(t : ℂ))‖ ≤ ∑ k, ‖a k‖ := by
    calc
      _ ≤ ∑ k, ‖a k * Complex.exp ((ω k : ℂ)*I*(t : ℂ))‖ := norm_sum_le _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro k _
        rw [norm_mul, RHTower.norm_exp_real_mul_I_mul_real, mul_one]
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun k : Fin n => ‖a k‖)
  simp only [Finset.card_univ, Fintype.card_fin] at hcs
  calc
    _ ≤ (∑ k, ‖a k‖)^2 := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ ≤ (n : ℝ) * ∑ k, ‖a k‖^2 := hcs

private theorem norm_sq_trig_test_le {n : ℕ} (a : Fin n → ℂ) (ω : Fin n → ℝ)
    (ha : ∑ k, ‖a k‖^2 ≤ 1) (t : ℝ) :
    ‖∑ k, a k * Complex.exp ((ω k : ℂ)*I*(t : ℂ))‖^2 ≤ (n : ℝ) := by
  calc
    _ ≤ (n : ℝ) * ∑ k, ‖a k‖^2 := norm_sq_trig_test_le_energy a ω t
    _ ≤ (n : ℝ) * 1 := mul_le_mul_of_nonneg_left ha (Nat.cast_nonneg n)
    _ = _ := mul_one _

/-- Every normalized growing trigonometric test with `o(T²)` terms has the same
quadratic zeta mean after finite symmetric relocation. Frequencies may vary with `T`. -/
theorem relocation_preserves_growing_trigonometric_tests (ρ : ℂ) (γ₁ γ₂ : ℝ)
    {σ : ℝ} (hσ : 1/2 < σ) (hσ1 : σ ≠ 1)
    (N : ℝ → ℕ) (a : (T : ℝ) → Fin (N T) → ℂ) (ω : (T : ℝ) → Fin (N T) → ℝ)
    (ha : ∀ T, ∑ k, ‖a T k‖^2 ≤ 1)
    (hN : Tendsto (fun T : ℝ => (N T : ℝ) / T^2) atTop (𝓝 0)) :
    Tendsto (fun T : ℝ => (∫ t in T..2*T,
      (‖relocatedZeta ρ γ₁ γ₂ ((σ : ℂ) + (t : ℂ)*I)‖^2 -
        ‖riemannZeta ((σ : ℂ) + (t : ℂ)*I)‖^2) *
          ‖∑ k, a T k * Complex.exp ((ω T k : ℂ)*I*(t : ℂ))‖^2) / T)
      atTop (𝓝 0) := by
  apply relocation_preserves_growing_weighted_mean ρ γ₁ γ₂ hσ hσ1
    (N := fun T => (N T : ℝ))
  · intro T
    fun_prop
  · exact fun _ _ => sq_nonneg _
  · exact fun T => Nat.cast_nonneg (N T)
  · intro T t _ _
    exact norm_sq_trig_test_le (a T) (ω T) (ha T) t
  · exact hN

private theorem relocation_den_norm_lower (γ₁ γ₂ σ t : ℝ)
    (ht : 2*(|γ₁|+|γ₂|+1) ≤ t) :
    (t/2)^4 ≤ ‖zeroRelocationDen γ₁ γ₂ ((σ : ℂ) + (t : ℂ)*I)‖ := by
  let s : ℂ := (σ : ℂ) + (t : ℂ)*I
  have ht0 : 0 ≤ t := by linarith only [abs_nonneg γ₁, abs_nonneg γ₂, ht]
  have hroot (a : ℂ) (ha : |a.im| ≤ t/2) : t/2 ≤ ‖s-a‖ := by
    have hi : (s-a).im = t-a.im := by simp [s]
    have hb := (le_abs_self a.im).trans ha
    have hn := Complex.abs_im_le_norm (s-a)
    rw [hi] at hn
    exact (show t/2 ≤ t-a.im by linarith only [hb]).trans ((le_abs_self _).trans hn)
  have hγ₁ : |γ₁| ≤ t/2 := by linarith only [ht, abs_nonneg γ₂]
  have hγ₂ : |γ₂| ≤ t/2 := by linarith only [ht, abs_nonneg γ₁]
  have h₁ := hroot (1/2 + I*γ₁) (by simpa using hγ₁)
  have h₂ := hroot (1/2 - I*γ₁) (by simpa using hγ₁)
  have h₃ := hroot (1/2 + I*γ₂) (by simpa using hγ₂)
  have h₄ := hroot (1/2 - I*γ₂) (by simpa using hγ₂)
  have h := mul_le_mul
    (mul_le_mul (mul_le_mul h₁ h₂ (by positivity) (norm_nonneg _))
      h₃ (by positivity) (by positivity)) h₄ (by positivity) (by positivity)
  calc (t/2)^4 = ((t/2)*(t/2)*(t/2))*(t/2) := by ring
    _ ≤ _ := h
    _ = _ := by simp only [zeroRelocationDen, norm_mul, s]

/-- Quadratic decay of the multiplier is uniform on a closed strip containing the line. -/
theorem exists_uniform_relocation_error_bound (ρ : ℂ) (γ₁ γ₂ : ℝ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ σ t : ℝ, 3/8 ≤ σ → σ ≤ 5/8 →
      2*(|γ₁|+|γ₂|+1) ≤ t →
        t^2 * ‖zeroRelocationFactor ρ γ₁ γ₂ ((σ : ℂ) + (t : ℂ)*I)-1‖ ≤ D := by
  let A := relocationQuadraticCoefficient ρ γ₁ γ₂
  let B := relocationQuarticCoefficient ρ γ₁ γ₂
  let K := 4*|A|+|B|
  refine ⟨16*K, by dsimp [K]; positivity, ?_⟩
  intro σ t hσ₁ hσ₂ ht
  have ht1 : 1 ≤ t := by linarith only [ht, abs_nonneg γ₁, abs_nonneg γ₂]
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht1
  have ht2 : 1 ≤ t^2 := by simpa using pow_le_pow_left₀ zero_le_one ht1 2
  let s : ℂ := (σ : ℂ) + (t : ℂ)*I
  have hw : ‖s-1/2‖ ≤ 2*t := by
    have he : s-1/2 = ((σ-1/2 : ℝ) : ℂ) + (t : ℂ)*I := by
      dsimp [s]; push_cast; ring
    have hσ : |σ-1/2| ≤ 1 := abs_le.mpr ⟨by linarith only [hσ₁], by linarith only [hσ₂]⟩
    rw [he]
    refine (norm_add_le _ _).trans ?_
    simp only [norm_mul, norm_real, Real.norm_eq_abs, norm_I, mul_one, abs_of_pos ht0]
    linarith only [hσ, ht1]
  have hnum : ‖(A : ℂ)*(s-1/2)^2 + (B : ℂ)‖ ≤ K*t^2 := by
    calc
      _ ≤ ‖(A : ℂ)*(s-1/2)^2‖ + ‖(B : ℂ)‖ := norm_add_le _ _
      _ = |A| * ‖s-1/2‖^2 + |B| := by
        rw [norm_mul, norm_pow, norm_real, norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ |A| *(2*t)^2 + |B| *t^2 :=
        add_le_add (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hw 2)
          (abs_nonneg A)) (by simpa only [mul_one] using mul_le_mul_of_nonneg_left ht2 (abs_nonneg B))
      _ = _ := by dsimp [K]; ring
  have hd := relocation_den_norm_lower γ₁ γ₂ σ t ht
  have hd0 : 0 < ‖zeroRelocationDen γ₁ γ₂ s‖ :=
    (pow_pos (half_pos ht0) 4).trans_le hd
  have hden : zeroRelocationDen γ₁ γ₂ s ≠ 0 := norm_pos_iff.mp hd0
  change t^2 * ‖zeroRelocationFactor ρ γ₁ γ₂ s-1‖ ≤ _
  rw [zeroRelocationFactor_sub_one ρ s γ₁ γ₂ hden, norm_div]
  calc
    _ ≤ t^2 * ((K*t^2) / (t/2)^4) :=
      mul_le_mul_of_nonneg_left
        ((div_le_div_of_nonneg_right hnum hd0.le).trans
          (div_le_div_of_nonneg_left (by dsimp [K]; positivity)
            (pow_pos (half_pos ht0) 4) hd)) (sq_nonneg t)
    _ = _ := by field_simp [ht0.ne'] <;> ring

/-- Uniform convexity and quadratic relocation decay give `O(1/t)` change in
zeta's squared modulus, including on the critical line. -/
theorem exists_uniform_relocatedZeta_normSq_error_bound (ρ : ℂ) (γ₁ γ₂ : ℝ) :
    ∃ C L : ℝ, 0 ≤ C ∧ 1 ≤ L ∧ ∀ σ t : ℝ, 3/8 ≤ σ → σ ≤ 5/8 → L ≤ t →
      t * |‖relocatedZeta ρ γ₁ γ₂ ((σ : ℂ) + (t : ℂ)*I)‖^2 -
        ‖riemannZeta ((σ : ℂ) + (t : ℂ)*I)‖^2| ≤ C := by
  obtain ⟨D, hD, hrel⟩ := exists_uniform_relocation_error_bound ρ γ₁ γ₂
  obtain ⟨K, hK, hζ⟩ := RHTower.exists_norm_riemannZeta_le_convexity
    (η := 3/8) (by norm_num) (by norm_num)
  let L := max 8 (2*(|γ₁|+|γ₂|+1))
  refine ⟨K^2*(D+2)*D, L, by positivity, (by dsimp [L]; linarith only [le_max_left (8 : ℝ) (2*(|γ₁|+|γ₂|+1))]), ?_⟩
  intro σ t hσ₁ hσ₂ ht
  have ht8 : 8 ≤ t := (le_max_left _ _).trans ht
  have htR : 2*(|γ₁|+|γ₂|+1) ≤ t := (le_max_right _ _).trans ht
  have ht1 : 1 ≤ t := by linarith only [ht8]
  have ht0 : 0 < t := by linarith only [ht8]
  have ht2 : 1 ≤ t^2 := by simpa using pow_le_pow_left₀ zero_le_one ht1 2
  let s : ℂ := (σ : ℂ) + (t : ℂ)*I
  let m := zeroRelocationFactor ρ γ₁ γ₂ s
  have hz : ‖riemannZeta s‖ ≤ K*t^(1/2 : ℝ) :=
    (hζ σ t (by linarith only [hσ₁]) (by linarith only [hσ₂]) ht8).trans
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le ht1 (by linarith only [hσ₁])) hK.le)
  have hpow : (t^(1/2 : ℝ))^2 = t := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht0.le]
    norm_num
  have hz2 : ‖riemannZeta s‖^2 ≤ K^2*t := by
    simpa only [mul_pow, hpow] using pow_le_pow_left₀ (norm_nonneg _) hz 2
  have herr : t^2*‖m-1‖ ≤ D := hrel σ t hσ₁ hσ₂ htR
  have hmerr : ‖m-1‖ ≤ D :=
    (show ‖m-1‖ ≤ t^2*‖m-1‖ by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right ht2 (norm_nonneg (m-1))).trans herr
  have hm : ‖m‖ ≤ D+1 := by
    have h := norm_sub_norm_le m (1 : ℂ)
    rw [norm_one] at h
    linarith only [h, hmerr]
  have habs : |‖m‖-1| ≤ ‖m-1‖ := by
    have h₁ := norm_sub_norm_le m (1 : ℂ)
    have h₂ := norm_sub_norm_le (1 : ℂ) m
    rw [norm_one] at h₁ h₂
    rw [norm_sub_rev] at h₂
    exact abs_le.mpr ⟨by linarith only [h₂], h₁⟩
  have hs : |‖m‖^2-1| ≤ (D+2)*‖m-1‖ := by
    rw [show ‖m‖^2-1 = (‖m‖-1)*(‖m‖+1) by ring, abs_mul,
      abs_of_nonneg (by positivity : 0 ≤ ‖m‖+1)]
    have h := mul_le_mul habs (show ‖m‖+1 ≤ D+2 by linarith only [hm])
      (by positivity : 0 ≤ ‖m‖+1) (norm_nonneg (m-1))
    simpa only [mul_comm ‖m-1‖ (D+2)] using h
  change t * |‖riemannZeta s*m‖^2-‖riemannZeta s‖^2| ≤ _
  rw [norm_mul, mul_pow,
    show ‖riemannZeta s‖^2*‖m‖^2-‖riemannZeta s‖^2 =
      ‖riemannZeta s‖^2*(‖m‖^2-1) by ring,
    abs_mul, abs_of_nonneg (sq_nonneg _)]
  calc
    _ ≤ t*((K^2*t)*((D+2)*‖m-1‖)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul hz2 hs (abs_nonneg _) (by positivity)) ht0.le
    _ = K^2*(D+2)*(t^2*‖m-1‖) := by ring
    _ ≤ K^2*(D+2)*D := mul_le_mul_of_nonneg_left herr (by positivity)

/-- Quadratic tests with term count times coefficient energy `o(T)` remain blind
to relocation even on arbitrary moving lines in a strip containing the critical line. -/
theorem relocation_preserves_short_tests_on_moving_lines (ρ : ℂ) (γ₁ γ₂ : ℝ)
    (σ : ℝ → ℝ) (hσ : ∀ T, σ T ∈ Icc (3/8 : ℝ) (5/8))
    (N : ℝ → ℕ) (a : (T : ℝ) → Fin (N T) → ℂ) (ω : (T : ℝ) → Fin (N T) → ℝ)
    (hN : Tendsto (fun T : ℝ => ((N T : ℝ)*(∑ k, ‖a T k‖^2))/T) atTop (𝓝 0)) :
    Tendsto (fun T : ℝ => (∫ t in T..2*T,
      (‖relocatedZeta ρ γ₁ γ₂ ((σ T : ℂ) + (t : ℂ)*I)‖^2 -
        ‖riemannZeta ((σ T : ℂ) + (t : ℂ)*I)‖^2) *
          ‖∑ k, a T k * Complex.exp ((ω T k : ℂ)*I*(t : ℂ))‖^2) / T)
      atTop (𝓝 0) := by
  obtain ⟨C, L, hC, hL, herror⟩ := exists_uniform_relocatedZeta_normSq_error_bound ρ γ₁ γ₂
  let B : ℝ → ℝ := fun T => (N T : ℝ)*(∑ k, ‖a T k‖^2)
  refine squeeze_zero_norm' (a := fun T => C*(B T/T)) ?_
    (by simpa only [mul_zero] using hN.const_mul C)
  filter_upwards [eventually_ge_atTop L] with T hT
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one (hL.trans hT)
  have hTT : T ≤ 2*T := by linarith only [hT0]
  have hi : ‖∫ t in T..2*T,
      (‖relocatedZeta ρ γ₁ γ₂ ((σ T : ℂ) + (t : ℂ)*I)‖^2 -
        ‖riemannZeta ((σ T : ℂ) + (t : ℂ)*I)‖^2) *
          ‖∑ k, a T k * Complex.exp ((ω T k : ℂ)*I*(t : ℂ))‖^2‖ ≤
      (C*B T/T)*|2*T-T| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro t ht
    rw [Set.uIoc_of_le hTT] at ht
    have he := herror (σ T) t (hσ T).1 (hσ T).2 (hT.trans ht.1.le)
    have he' : |‖relocatedZeta ρ γ₁ γ₂ ((σ T : ℂ) + (t : ℂ)*I)‖^2 -
        ‖riemannZeta ((σ T : ℂ) + (t : ℂ)*I)‖^2| ≤ C/T := by
      apply (le_div_iff₀ hT0).mpr
      have hh := mul_le_mul_of_nonneg_right ht.1.le
        (abs_nonneg (‖relocatedZeta ρ γ₁ γ₂ ((σ T : ℂ) + (t : ℂ)*I)‖^2 -
          ‖riemannZeta ((σ T : ℂ) + (t : ℂ)*I)‖^2))
      nlinarith only [hh, he]
    rw [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (sq_nonneg ‖∑ k, a T k * Complex.exp ((ω T k : ℂ)*I*(t : ℂ))‖)]
    calc
      _ ≤ (C/T)*B T :=
        mul_le_mul he' (norm_sq_trig_test_le_energy (a T) (ω T) t)
          (sq_nonneg _) (div_nonneg hC hT0.le)
      _ = _ := by ring
  rw [show |2*T-T| = T by rw [show 2*T-T = T by ring, abs_of_pos hT0]] at hi
  rw [norm_div, Real.norm_of_nonneg hT0.le]
  calc
    _ ≤ ((C*B T/T)*T)/T := div_le_div_of_nonneg_right hi hT0.le
    _ = _ := by field_simp [hT0.ne']

/-- Actual critical-line donor pairs admit a residue-preserving off-line relocation
invisible to every short quadratic test on moving lines near the critical line. -/
theorem exists_normalized_relocation_invisible_to_short_tests :
    ∃ γ₁ γ₂ : ℝ, 1 < γ₁ ∧ γ₁ < γ₂ ∧
      riemannZeta (1/2 + (γ₁ : ℂ)*I) = 0 ∧
      riemannZeta (1/2 + (γ₂ : ℂ)*I) = 0 ∧
      ∃ ρ : ℂ, ρ.re = 3/4 ∧ 0 < ρ.im ∧
        zeroRelocationFactor ρ γ₁ γ₂ 0 = 1 ∧
        zeroRelocationFactor ρ γ₁ γ₂ 1 = 1 ∧
        relocatedZeta ρ γ₁ γ₂ ρ = 0 ∧
        (∀ s : ℂ, completedRiemannZeta (1-s) * zeroRelocationFactor ρ γ₁ γ₂ (1-s) =
          completedRiemannZeta s * zeroRelocationFactor ρ γ₁ γ₂ s) ∧
        ∀ (σ : ℝ → ℝ), (∀ T, σ T ∈ Icc (3/8 : ℝ) (5/8)) →
        ∀ (N : ℝ → ℕ) (a : (T : ℝ) → Fin (N T) → ℂ)
          (ω : (T : ℝ) → Fin (N T) → ℝ),
        Tendsto (fun T : ℝ => ((N T : ℝ)*(∑ k, ‖a T k‖^2))/T) atTop (𝓝 0) →
        Tendsto (fun T : ℝ => (∫ t in T..2*T,
          (‖relocatedZeta ρ γ₁ γ₂ ((σ T : ℂ) + (t : ℂ)*I)‖^2 -
            ‖riemannZeta ((σ T : ℂ) + (t : ℂ)*I)‖^2) *
              ‖∑ k, a T k * Complex.exp ((ω T k : ℂ)*I*(t : ℂ))‖^2) / T)
          atTop (𝓝 0) := by
  obtain ⟨γ₁, γ₂, hγ₁, hγ₂, hz₁, hz₂, hheight, -, h₀, h₁, -⟩ :=
    exists_normalizedRelocation_signed_density
  refine ⟨γ₁, γ₂, hγ₁, hγ₂, hz₁, hz₂, normalizedRelocationTarget γ₁ γ₂,
    normalizedRelocationTarget_re γ₁ γ₂, ?_, h₀, h₁, ?_, ?_, ?_⟩
  · simpa only [normalizedRelocationTarget_im] using hheight
  · unfold relocatedZeta
    rw [normalizedRelocation_target_zero, mul_zero]
  · exact completedRiemannZeta_mul_zeroRelocationFactor_one_sub
      (normalizedRelocationTarget γ₁ γ₂) γ₁ γ₂
  · intro σ hσ N a ω hN
    exact relocation_preserves_short_tests_on_moving_lines
      (normalizedRelocationTarget γ₁ γ₂) γ₁ γ₂ σ hσ N a ω hN


end GaloisForLFunctions.ArithmeticPositiveDuality
