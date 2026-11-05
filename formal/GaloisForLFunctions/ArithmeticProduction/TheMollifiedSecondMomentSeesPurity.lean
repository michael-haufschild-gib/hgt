import GaloisForLFunctions.ArithmeticProduction.LongMollifiersImplyCriticalClustering
import GaloisForLFunctions.ArithmeticProduction.ImpureEulerFactorsPassEveryUpperBound
import GaloisForLFunctions.RHTower.OuterDecompositionLawMollifiedProduct
import GaloisForLFunctions.RHTower.MollifierLineLogMeanFloor

/-!
# The mollified second moment sees purity

Every upper bound for `ζ` on the line survives an impure factor `f(s) = 1 − c p^{−s}`, `c > √p`.  The mollified second moment does not.

**Theorem** (`impure_second_moment_floor`).  For every `ε > 0`, every real mollifier `M` with `b₁ = 1`, `|b_n| ≤ 1` of length `exp(δT)`, and all large `T`,

  `∫_T^{2T} |ζ f M(½+it)|² dt ≥ (1 − ε) (c²/p) T`.

The proof is concavity of the logarithm: the log-mean of `f` is `log(c/√p)`, and those of `ζ` and `M` are at least `−o(1)`.

So the law "second moment tends to `1`" fails on the mimic at every length (`not_secondMomentLaw_impure`): a proof of it must use the size of the Euler factor at every single prime.
Together with the necessary-length law it brackets the question from both sides: it needs unbounded length, and it needs local purity.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.ArithmeticProduction

open _root_.RHTower

/-- Concavity of the logarithm, in the tangent form at `r²`. -/
private theorem log_tangent_pointwise {A B F r : ℝ} (hA : 0 < A) (hB : 0 < B) (hF : 0 < F) (hr : 0 < r) :
    r ^ 2 * (1 - 2 * Real.log r) + 2 * r ^ 2 * (Real.log A + Real.log B + Real.log F) ≤
      (A * B) ^ 2 * F ^ 2 := by
  have hy : 0 < (A * B) ^ 2 * F ^ 2 / r ^ 2 := by positivity
  have hlog := Real.log_le_sub_one_of_pos hy
  rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow, Real.log_pow, Real.log_mul hA.ne' hB.ne'] at hlog
  push_cast at hlog
  have hmul := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ r ^ 2)
  have hcancel : r ^ 2 * ((A * B) ^ 2 * F ^ 2 / r ^ 2 - 1) = (A * B) ^ 2 * F ^ 2 - r ^ 2 := by
    field_simp
  rw [hcancel] at hmul
  have hexp : r ^ 2 * (1 - 2 * Real.log r) + 2 * r ^ 2 * (Real.log A + Real.log B + Real.log F) =
      r ^ 2 + r ^ 2 * (2 * (Real.log A + Real.log B) + 2 * Real.log F - 2 * Real.log r) := by ring
  rw [hexp]
  linarith

/-- Concavity of the logarithm, integrated over the segment. -/
private theorem log_tangent_integrated {p : ℕ} (hp : 1 < p) {c : ℝ} (hc : √(p : ℝ) < c) (b : ℕ → ℂ) {N : ℕ}
    (hN : 1 ≤ N) (hb1 : b 1 = 1) (hb : ∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1) {T₁ T₂ : ℝ} (h20 : 20 ≤ T₁)
    (hT : T₁ < T₂) :
    (c / √(p : ℝ)) ^ 2 * (1 - 2 * Real.log (c / √(p : ℝ))) * (T₂ - T₁) + 2 * (c / √(p : ℝ)) ^ 2 *
        ((∫ t in T₁..T₂, Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖) +
          (∫ t in T₁..T₂, Real.log ‖edPoly b (Finset.Icc 1 N) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖) +
          ∫ t in T₁..T₂, Real.log ‖impureFactor p c (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖) ≤
      ∫ t in T₁..T₂, ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
        edPoly b (Finset.Icc 1 N) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 *
          ‖impureFactor p c (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hs0 : 0 < √(p : ℝ) := Real.sqrt_pos.mpr hp0
  have hc0 : 0 < c := by linarith
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = c / √(p : ℝ) := ⟨_, rfl⟩
  rw [← hr]
  have hr0 : 0 < r := by rw [hr]; positivity
  have hs : ∀ n ∈ Finset.Icc 1 N, 1 ≤ n := fun n hn => (Finset.mem_Icc.mp hn).1
  have hne : ∃ z : ℂ, edPoly b (Finset.Icc 1 N) z ≠ 0 := by
    refine ⟨((15 / 2 : ℝ) : ℂ), fun h0 => ?_⟩
    have h := norm_edPoly_sub_one_le_half_of_six_le b hs
      (Finset.mem_Icc.mpr ⟨le_rfl, hN⟩) hb1 hb (z := ((15 / 2 : ℝ) : ℂ)) (by simp; norm_num)
    rw [h0] at h
    norm_num at h
  have h1 := intervalIntegrable_log_norm_riemannZeta_line T₁ T₂
  have h2 := intervalIntegrable_log_norm_vertical_of_entire
    (analyticOnNhd_edPoly b hs) (1 / 2) T₁ T₂
  have h3 := intervalIntegrable_log_norm_impureFactor hp hc T₁ T₂
  have hw : IntervalIntegrable (fun t : ℝ => Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ +
      Real.log ‖edPoly b (Finset.Icc 1 N) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ +
      Real.log ‖impureFactor p c (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖) volume T₁ T₂ := (h1.add h2).add h3
  -- the factor never vanishes
  have hfne : ∀ t : ℝ, ‖impureFactor p c (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≠ 0 := by
    intro t h0
    have h4 : ∀ q lam : ℝ, 0 ≤ q → q < 1 → ‖1 - (q : ℂ) * Complex.exp (((lam * t : ℝ) : ℂ) * I)‖ ≠ 0 := by
      intro q lam hq0 hq1 h5
      have h6 := norm_eq_zero.mp h5
      have h7 : (q : ℂ) * Complex.exp (((lam * t : ℝ) : ℂ) * I) = 1 := by
        rw [sub_eq_zero] at h6
        exact h6.symm
      have h8 := congrArg norm h7
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hq0, Complex.norm_exp_ofReal_mul_I,
        mul_one, norm_one] at h8
      linarith
    have hf := norm_eq_zero.mp h0
    unfold impureFactor at hf
    -- on the line `|c p^{−s}| = c/√p > 1`
    have h9 : ‖(c : ℂ) * (p : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I))‖ = 1 := by
      rw [sub_eq_zero] at hf
      rw [← hf, norm_one]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc0.le,
      Complex.norm_natCast_cpow_of_pos (by omega)] at h9
    simp only [neg_add_rev, Complex.add_re, Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
      Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self,
      neg_zero, zero_add] at h9
    have h10 : (p : ℝ) ^ (-(1 / 2 : ℝ)) = (√(p : ℝ))⁻¹ := by
      rw [Real.rpow_neg hp0.le, Real.sqrt_eq_rpow]
    rw [h10] at h9
    have h11 : c * (√(p : ℝ))⁻¹ = 1 := h9
    have h12 : c = √(p : ℝ) := by
      field_simp at h11
      exact h11
    linarith
  have hcontG : Continuous fun t : ℝ => ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
      edPoly b (Finset.Icc 1 N) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 :=
    continuous_norm_sq_zeta_mul_edPoly b N (by norm_num)
  have hcontF : Continuous fun t : ℝ => ‖impureFactor p c (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
    refine ((continuous_const.sub (continuous_const.mul ?_)).norm).pow 2
    exact Continuous.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast hp0.ne'))
  have hint : IntervalIntegrable (fun t : ℝ => r ^ 2 * (1 - 2 * Real.log r) + 2 * r ^ 2 *
      (Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ +
        Real.log ‖edPoly b (Finset.Icc 1 N) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ +
        Real.log ‖impureFactor p c (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖)) volume T₁ T₂ :=
    intervalIntegrable_const.add (hw.const_mul _)
  have hcontGF : Continuous fun t : ℝ => ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
      edPoly b (Finset.Icc 1 N) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 *
        ‖impureFactor p c (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 := hcontG.mul hcontF
  have hmono : (∫ t in T₁..T₂, r ^ 2 * (1 - 2 * Real.log r) + 2 * r ^ 2 *
      (Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ +
        Real.log ‖edPoly b (Finset.Icc 1 N) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ +
        Real.log ‖impureFactor p c (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖)) ≤
      ∫ t in T₁..T₂, ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
        edPoly b (Finset.Icc 1 N) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 *
          ‖impureFactor p c (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
    refine intervalIntegral.integral_mono_ae_restrict hT.le hint (hcontGF.intervalIntegrable _ _) ?_
    have hζ := (finite_zetaLine_zeros h20 hT).measure_zero volume
    have hΨ := (finite_edPolyLine_zeros b hs hne T₁ T₂).measure_zero volume
    rw [MeasureTheory.measure_eq_zero_iff_ae_notMem] at hζ hΨ
    rw [Filter.EventuallyLE, MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hζ, hΨ] with t htζ htΨ hIcc
    have hζ0 : 0 < ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ :=
      norm_pos_iff.mpr fun h => htζ ⟨hIcc, h⟩
    have hΨ0 : 0 < ‖edPoly b (Finset.Icc 1 N) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ :=
      norm_pos_iff.mpr fun h => htΨ ⟨hIcc, h⟩
    have hf0 : 0 < ‖impureFactor p c (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm (hfne t))
    rw [norm_mul]
    exact log_tangent_pointwise hζ0 hΨ0 hf0 hr0
  rw [intervalIntegral.integral_add intervalIntegrable_const (hw.const_mul _),
    intervalIntegral.integral_const, smul_eq_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (h1.add h2) h3, intervalIntegral.integral_add h1 h2] at hmono
  have hreorder : (T₂ - T₁) * (r ^ 2 * (1 - 2 * Real.log r)) = r ^ 2 * (1 - 2 * Real.log r) * (T₂ - T₁) := by
    ring
  rw [hreorder] at hmono
  exact hmono

/-- **The floor of the mollified second moment of an impure factor.** -/
theorem impure_second_moment_floor {p : ℕ} (hp : 1 < p) {c : ℝ} (hc : √(p : ℝ) < c) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ T : ℝ in atTop, ∀ (b : ℕ → ℂ) (N : ℕ), 1 ≤ N → b 1 = 1 →
      (∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1) →
      (∀ n ∈ Finset.Icc 1 N, (starRingEnd ℂ) (b n) = b n) → Real.log N ≤ δ * T →
      (1 - ε) * (c / √(p : ℝ)) ^ 2 * T ≤
        ∫ t in T..(2 * T), ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
          edPoly b (Finset.Icc 1 N) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 *
            ‖impureFactor p c (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
  obtain ⟨C₁, K₁, hC₁, hK₁, hζfloor⟩ := exists_zetaLine_logMean_floor
  obtain ⟨C₂, K₂, hC₂, hK₂, hMfloor⟩ := exists_edPoly_line_logMean_floor
  obtain ⟨B₀, hB₀⟩ : ∃ B₀ : ℝ, B₀ = 2 / Real.log p * (1 - (c / √(p : ℝ))⁻¹)⁻¹ := ⟨_, rfl⟩
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
  have hlogp : 0 < Real.log p := Real.log_pos hp1
  have hp0 : (0 : ℝ) < p := by linarith
  have hs0 : 0 < √(p : ℝ) := Real.sqrt_pos.mpr hp0
  have hc0 : 0 < c := by linarith
  have hr1 : 1 < c / √(p : ℝ) := by rw [one_lt_div hs0]; exact hc
  have hq1 : (c / √(p : ℝ))⁻¹ < 1 := inv_lt_one_of_one_lt₀ hr1
  have hB₀0 : 0 ≤ B₀ := by
    rw [hB₀]
    have : 0 < 1 - (c / √(p : ℝ))⁻¹ := by linarith
    positivity
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = 2 + 2 * (B₀ + C₁ + K₁ + C₂) := ⟨_, rfl⟩
  have hD0 : 0 < D := by rw [hD]; positivity
  refine ⟨ε / (4 * (10 * K₂ + 1)), by positivity, ?_⟩
  filter_upwards [eventually_log_pow_mul_exp_le 1 (c := 1) (ε := ε / (8 * (K₁ + 1))) one_pos (by positivity),
    eventually_ge_atTop (22 : ℝ), eventually_ge_atTop (8 * D / ε)] with T hsm hT22 hTD
    b N hN hb1 hb hbr hlogN
  have hT0 : 0 < T := by linarith
  obtain ⟨T₁, hT₁, T₂, hT₂, hs1, hs2⟩ := exists_admissible_slices (b := b) (N := N) hN hb1 hb
    (A₁ := T) (B₁ := T + 1) (A₂ := 2 * T - 1) (B₂ := 2 * T)
    (by linarith) (by linarith) (by linarith) (by linarith)
  obtain ⟨hT₁a, hT₁b⟩ := hT₁
  obtain ⟨hT₂a, hT₂b⟩ := hT₂
  have hT12 : T₁ < T₂ := by linarith
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = c / √(p : ℝ) := ⟨_, rfl⟩
  rw [← hr] at hB₀ hr1 ⊢
  have hr0 : 0 < r := by linarith
  have hsub : Set.Icc (1 / 2 : ℝ) (15 / 2 : ℝ) ⊆ Set.Icc (1 / 4 : ℝ) (15 / 2 : ℝ) :=
    Set.Icc_subset_Icc (by norm_num) le_rfl
  have hMb1 : (1 : ℝ) ≤ (N : ℝ) ^ 5 := one_le_pow₀ (by exact_mod_cast hN)
  have h1 := hζfloor T₁ T₂ (by linarith) hT12 (fun x hx => (hs1 x (hsub hx)).1)
    (fun x hx => (hs2 x (hsub hx)).1)
  have h2 := hMfloor b N hN hb1 hb hbr ((N : ℝ) ^ 5) hMb1 (sum_norm_mul_rpow_four_le hb) T₁ T₂ hT12
    (fun x hx => (hs1 x (hsub hx)).2) (fun x hx => (hs2 x (hsub hx)).2)
  have h3 := (abs_le.mp (abs_integral_log_norm_impureFactor_sub_le hp hc hT12.le)).1
  rw [← hr, ← hB₀] at h3
  have htan := log_tangent_integrated hp hc b hN hb1 hb (by linarith) hT12
  rw [← hr] at htan
  -- the second moment on the inner segment
  have hcontG := continuous_norm_sq_zeta_mul_edPoly b N (c := 1 / 2) (by norm_num)
  have hcontF : Continuous fun t : ℝ => ‖impureFactor p c (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
    refine ((continuous_const.sub (continuous_const.mul ?_)).norm).pow 2
    exact Continuous.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast hp0.ne'))
  have hcontGF : Continuous fun t : ℝ => ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
      edPoly b (Finset.Icc 1 N) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 *
        ‖impureFactor p c (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 := hcontG.mul hcontF
  have hnonneg : ∀ t : ℝ, (0 : ℝ) ≤ ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
      edPoly b (Finset.Icc 1 N) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 *
        ‖impureFactor p c (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 := fun t => by positivity
  have hmono := intervalIntegral.integral_mono_interval (μ := volume) hT₁a.le hT12.le hT₂b.le
    (Filter.Eventually.of_forall hnonneg) (hcontGF.intervalIntegrable T (2 * T))
  refine le_trans ?_ hmono
  refine le_trans ?_ htan
  -- arithmetic
  obtain ⟨I₁, hI₁⟩ : ∃ I₁ : ℝ, I₁ = ∫ t in T₁..T₂, Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ := ⟨_, rfl⟩
  obtain ⟨I₂, hI₂⟩ : ∃ I₂ : ℝ, I₂ = ∫ t in T₁..T₂, Real.log ‖edPoly b (Finset.Icc 1 N) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ := ⟨_, rfl⟩
  obtain ⟨I₃, hI₃⟩ : ∃ I₃ : ℝ, I₃ = ∫ t in T₁..T₂, Real.log ‖impureFactor p c (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ := ⟨_, rfl⟩
  rw [← hI₁] at h1
  rw [← hI₂] at h2
  rw [← hI₃] at h3
  rw [← hI₁, ← hI₂, ← hI₃]
  have hlogT₂ : Real.log T₂ ≤ Real.log T + 1 := by
    have h4 : Real.log T₂ ≤ Real.log (2 * T) := Real.log_le_log (by linarith) hT₂b.le
    rw [Real.log_mul two_ne_zero hT0.ne'] at h4
    have h5 := Real.log_two_lt_d9
    linarith
  have hlogMb : Real.log ((N : ℝ) ^ 5) = 5 * Real.log N := by
    rw [Real.log_pow]
    norm_num
  rw [hlogMb] at h2
  have hlogT : Real.log T ≤ ε / (8 * (K₁ + 1)) * T := by
    have hTe : Real.exp (-(1 * Real.log T)) = T⁻¹ := by
      rw [one_mul, Real.exp_neg, Real.exp_log hT0]
    rw [hTe, pow_one, ← div_eq_mul_inv, div_le_iff₀ hT0] at hsm
    exact hsm
  have hK₁T : K₁ * Real.log T ≤ ε / 8 * T := by
    have h4 := mul_le_mul_of_nonneg_left hlogT hK₁.le
    refine h4.trans ?_
    have h5 : K₁ * (ε / (8 * (K₁ + 1)) * T) = (K₁ / (K₁ + 1)) * (ε / 8 * T) := by
      field_simp
    rw [h5]
    refine mul_le_of_le_one_left (by positivity) ?_
    rw [div_le_one (by positivity)]
    linarith
  have hK₁T₂ : K₁ * Real.log T₂ ≤ K₁ * Real.log T + K₁ := by
    calc K₁ * Real.log T₂ ≤ K₁ * (Real.log T + 1) := mul_le_mul_of_nonneg_left hlogT₂ hK₁.le
      _ = _ := by ring
  have hK₂N : K₂ * (5 * Real.log N) ≤ ε / 8 * T := by
    have h4 : K₂ * (5 * Real.log N) ≤ K₂ * (5 * (ε / (4 * (10 * K₂ + 1)) * T)) :=
      mul_le_mul_of_nonneg_left (by linarith) hK₂.le
    refine h4.trans ?_
    have h5 : K₂ * (5 * (ε / (4 * (10 * K₂ + 1)) * T)) = (10 * K₂ / (10 * K₂ + 1)) * (ε / 8 * T) := by
      field_simp
      ring
    rw [h5]
    refine mul_le_of_le_one_left (by positivity) ?_
    rw [div_le_one (by positivity)]
    linarith
  have hDT : D ≤ ε / 8 * T := by
    have h4 := (div_le_iff₀ hε).mp hTD
    linarith
  -- combine: `L + 2(I₁ + I₂ + I₃ − L log r) ≥ (1 − ε) T`
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = T₂ - T₁ := ⟨_, rfl⟩
  rw [← hL] at h3 ⊢
  have hLT : T - 2 ≤ L := by rw [hL]; linarith
  have hsumI : -(B₀ + C₁ + K₁ * Real.log T₂ + C₂ + K₂ * (5 * Real.log N)) ≤
      I₁ + I₂ + I₃ - L * Real.log r := by linarith
  have hkey : (1 - ε) * T ≤ L + 2 * (I₁ + I₂ + I₃ - L * Real.log r) := by
    have hD2 : 2 + 2 * (B₀ + C₁ + K₁ + C₂) = D := hD.symm
    have hε1 : ε * T = 8 * (ε / 8 * T) := by ring
    have hε2 : (1 - ε) * T = T - ε * T := by ring
    linarith
  have hexp : r ^ 2 * (1 - 2 * Real.log r) * L + 2 * r ^ 2 * (I₁ + I₂ + I₃) =
      r ^ 2 * (L + 2 * (I₁ + I₂ + I₃ - L * Real.log r)) := by ring
  rw [hexp]
  calc (1 - ε) * r ^ 2 * T = r ^ 2 * ((1 - ε) * T) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hkey (by positivity)

/-- **The law fails on an impure factor, at every length.** -/
theorem not_secondMomentLaw_impure {p : ℕ} (hp : 1 < p) {c : ℝ} (hc : √(p : ℝ) < c) :
    ¬ ∀ ε : ℝ, 0 < ε → ∀ᶠ T : ℝ in atTop, ∃ (b : ℕ → ℂ) (N : ℕ), 1 ≤ N ∧ b 1 = 1 ∧
      (∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1) ∧
      (∀ n ∈ Finset.Icc 1 N, (starRingEnd ℂ) (b n) = b n) ∧ Real.log N ≤ ε * T ∧
      (∫ t in T..(2 * T), ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
          edPoly b (Finset.Icc 1 N) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 *
            ‖impureFactor p c (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤ (1 + ε) * T := by
  intro h
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hs0 : 0 < √(p : ℝ) := Real.sqrt_pos.mpr hp0
  have hr1 : 1 < c / √(p : ℝ) := by rw [one_lt_div hs0]; exact hc
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = c / √(p : ℝ) := ⟨_, rfl⟩
  rw [← hr] at hr1
  obtain ⟨ε₀, hε₀⟩ : ∃ ε₀ : ℝ, ε₀ = (r ^ 2 - 1) / (4 * r ^ 2) := ⟨_, rfl⟩
  have hr2 : 1 < r ^ 2 := by nlinarith
  have hε₀0 : 0 < ε₀ := by
    rw [hε₀]
    exact div_pos (by linarith) (by positivity)
  obtain ⟨δ, hδ, hfloor⟩ := impure_second_moment_floor hp hc hε₀0
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = min δ ((r ^ 2 - 1) / 2) := ⟨_, rfl⟩
  have hη0 : 0 < η := by
    rw [hη]
    exact lt_min hδ (by linarith)
  obtain ⟨T, ⟨b, N, hN, hb1, hb, hbr, hlogN, hmom⟩, hF, hT0⟩ :=
    ((h η hη0).and (hfloor.and (eventually_gt_atTop (0 : ℝ)))).exists
  have hηδ : η ≤ δ := by rw [hη]; exact min_le_left _ _
  have hηr : η ≤ (r ^ 2 - 1) / 2 := by rw [hη]; exact min_le_right _ _
  have h1 := hF b N hN hb1 hb hbr (hlogN.trans (mul_le_mul_of_nonneg_right hηδ hT0.le))
  rw [← hr] at h1
  have h2 := le_of_mul_le_mul_right (h1.trans hmom) hT0
  have h3 : (1 - ε₀) * r ^ 2 = r ^ 2 - (r ^ 2 - 1) / 4 := by
    rw [hε₀]
    field_simp
  rw [h3] at h2
  linarith

end GaloisForLFunctions.ArithmeticProduction
