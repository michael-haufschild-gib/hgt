import GaloisForLFunctions.HTGeometry.TestFunctionPerronShift

/-!
# Weighted `L¹` bounds for Mellin transforms of oscillating test functions

Let `f` be a test function on `[a, b]` (`0 < a ≤ b`) with `|f| ≤ B₀` and `|u f'(u)| ≤ B₁`.  For
`σ ≥ 0`, `0 ≤ κ < 1/2` and `T ≥ 1`,

`∫ (|t| + 1)^κ |𝓜f(σ + it)| dt ≤ C (B₀ + B₁/T) T^{κ + 1/2}`
(`integral_rpow_mul_norm_mellin_le`), with `C` depending only on `a, b, σ, κ`.

**Proof.**  Write `m(t) = |𝓜f(σ + it)|`.  Mellin–Plancherel bounds `∫ m² ≤ c₀ B₀²`, and since
`𝓜[u f'](s) = −s 𝓜f(s)`, also `∫ t² m² ≤ c₀ B₁²`.  Cauchy–Schwarz against the weight
`(1 + |t|/T)` gives `∫ (|t| + 1)^κ m ≤ (∫ T^{2κ}(1 + |t|/T)^{2κ−2})^{1/2} (2c₀(B₀² + B₁²/T²))^{1/2}`,
and the first integral is `T^{2κ+1} ∫ (1 + |u|)^{2κ−2} du`.

**The twist** `f_c(u) = F(u) e(c/u)` (`twist`) of a test function `F` is a test function on the
same interval with `|f_c| ≤ |F|_∞` and `|u f_c'| ≤ |u F'|_∞ + 2π|c| |F|_∞/a`
(`IsTest.twist`, `norm_mul_deriv_twist_le`).  So `∫ (|t| + 1)^κ |𝓜f_c(σ + it)| dt ≪ (1 + |c|)^{κ+1/2}`
(`exists_integral_twist_le`).  At a real point `ρ`, one integration by parts against
`d e(c/u) = −2πi c u^{−2} e(c/u) du` gives `|𝓜f_c(ρ)| ≪ 1/(1 + |c|)` (`exists_norm_mellin_twist_le`).
-/

open Set Function Filter Complex Real MeasureTheory Topology
open scoped Interval ContDiff

noncomputable section

namespace GaloisForLFunctions.HTGeometry.TestFunctionPerron

variable {f : ℝ → ℂ} {a b : ℝ}

/-- Square integrability of `𝓜f` on a vertical line. -/
theorem IsTest.integrable_norm_mellin_sq (hf : IsTest f a b) (σ : ℝ) :
    Integrable fun t : ℝ => ‖mellin f ((σ : ℂ) + t * I)‖ ^ 2 := by
  obtain ⟨C, hC0, hC⟩ := hf.exists_norm_mellin_le_decay |σ - 1|
  refine (integrable_inv_one_add_sq.const_mul (C ^ 2)).mono' ?_ ?_
  · exact ((hf.continuous_mellin_line σ).norm.pow 2).aestronglyMeasurable
  · filter_upwards with y
    have h := hC ((σ : ℂ) + y * I) (by simp)
    simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero,
      zero_add] at h
    have hy : 1 ≤ 1 + y ^ 2 := by nlinarith [sq_nonneg y]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc ‖mellin f ((σ : ℂ) + y * I)‖ ^ 2 ≤ (C / (1 + y ^ 2)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h 2
      _ = C ^ 2 * ((1 + y ^ 2)⁻¹ * (1 + y ^ 2)⁻¹) := by rw [div_pow]; field_simp
      _ ≤ C ^ 2 * ((1 + y ^ 2)⁻¹ * 1) := by
          gcongr
          exact inv_le_one_of_one_le₀ hy
      _ = C ^ 2 * (1 + y ^ 2)⁻¹ := by ring

/-- `|t| |𝓜f(σ + it)| ≤ |𝓜[u f'](σ + it)|`. -/
theorem IsTest.abs_mul_norm_mellin_le (hf : IsTest f a b) (σ t : ℝ) :
    |t| * ‖mellin f ((σ : ℂ) + t * I)‖ ≤
      ‖mellin (fun u => (u : ℂ) * deriv f u) ((σ : ℂ) + t * I)‖ := by
  rw [hf.mellin_eulerDeriv, norm_mul, norm_neg]
  have : |t| ≤ ‖(σ : ℂ) + t * I‖ := by
    have := Complex.abs_im_le_norm ((σ : ℂ) + t * I)
    simpa using this
  exact mul_le_mul_of_nonneg_right this (norm_nonneg _)

/-- The constant `∫ (1 + |u|)^{2κ−2} du`. -/
def weightIntegral (κ : ℝ) : ℝ := ∫ u : ℝ, (1 + |u|) ^ (2 * κ - 2)

theorem integrable_one_add_abs_rpow {r : ℝ} (hr : r < -1) :
    Integrable fun u : ℝ => (1 + |u|) ^ r := by
  have h : Integrable fun y : ℝ => (1 + ‖y‖) ^ (-(-r)) :=
    integrable_one_add_norm (by simp; linarith)
  refine h.congr (Eventually.of_forall fun y => ?_)
  simp only [Real.norm_eq_abs, neg_neg]

/-- `∫ (1 + |t|/T)^r dt = T ∫ (1 + |u|)^r du`. -/
theorem integral_one_add_abs_div_rpow {r T : ℝ} (hT : 0 < T) :
    ∫ t : ℝ, (1 + |t| / T) ^ r = T * ∫ u : ℝ, (1 + |u|) ^ r := by
  have h := Measure.integral_comp_div (fun u : ℝ => (1 + |u|) ^ r) T
  rw [abs_of_pos hT, smul_eq_mul] at h
  rw [← h]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [abs_div, abs_of_pos hT]

/-- **The weighted `L¹` bound.** -/
theorem integral_rpow_mul_norm_mellin_le (ha : 0 < a) (hab : a ≤ b) {σ κ : ℝ} (hσ : 0 ≤ σ)
    (hκ0 : 0 ≤ κ) (hκ : κ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : ℝ → ℂ, IsTest f a b → ∀ B₀ B₁ T : ℝ, 0 < B₀ → 0 ≤ B₁ → 1 ≤ T →
      (∀ u, ‖f u‖ ≤ B₀) → (∀ u : ℝ, ‖(u : ℂ) * deriv f u‖ ≤ B₁) →
      ∫ t : ℝ, (|t| + 1) ^ κ * ‖mellin f ((σ : ℂ) + t * I)‖ ≤
        C * (B₀ + B₁ / T) * T ^ (κ + 1 / 2) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  set c₀ : ℝ := 2 * π * (b ^ (2 * σ) * (Real.log b - Real.log a)) with hc₀
  have hlog : 0 ≤ Real.log b - Real.log a := by linarith [Real.log_le_log ha hab]
  have hc₀0 : 0 ≤ c₀ := by positivity
  set Iκ := weightIntegral κ with hIκ
  have hIκ0 : 0 ≤ Iκ := integral_nonneg fun u => by positivity
  refine ⟨(Iκ + 2 * c₀) / 2, by positivity, ?_⟩
  intro f hf B₀ B₁ T hB₀ hB₁ hT hf0 hf1
  have hT0 : 0 < T := by linarith
  set m : ℝ → ℝ := fun t => ‖mellin f ((σ : ℂ) + t * I)‖ with hm
  set n : ℝ → ℝ := fun t => ‖mellin (fun u => (u : ℂ) * deriv f u) ((σ : ℂ) + t * I)‖
    with hn
  set w : ℝ → ℝ := fun t => (|t| + 1) ^ κ with hw
  set v : ℝ → ℝ := fun t => 1 + |t| / T with hv
  have hv1 : ∀ t, 1 ≤ v t := fun t => by
    simp only [hv]; have : 0 ≤ |t| / T := by positivity
    linarith
  have hvpos : ∀ t, 0 < v t := fun t => lt_of_lt_of_le one_pos (hv1 t)
  -- Plancherel bounds
  have hP : ∫ t, m t ^ 2 ≤ c₀ * B₀ ^ 2 := by
    have := MellinPlancherel.integral_norm_sq_mellin_le hf.smooth ha hab hf.supp hσ hf0
    rw [hc₀]; simp only [hm]; linarith
  have hQ : ∫ t, n t ^ 2 ≤ c₀ * B₁ ^ 2 := by
    have := MellinPlancherel.integral_norm_sq_mellin_le hf.eulerDeriv.smooth ha hab
      hf.eulerDeriv.supp hσ hf1
    rw [hc₀]; simp only [hn]; linarith
  have hmInt : Integrable fun t => m t ^ 2 := hf.integrable_norm_mellin_sq σ
  have hnInt : Integrable fun t => n t ^ 2 := hf.eulerDeriv.integrable_norm_mellin_sq σ
  -- the weight
  have hwv : ∀ t, (w t / v t) ^ 2 ≤ T ^ (2 * κ) * v t ^ (2 * κ - 2) := by
    intro t
    have hle : |t| + 1 ≤ T * v t := by
      simp only [hv]; rw [mul_add, mul_div_cancel₀ _ hT0.ne']; linarith [abs_nonneg t]
    have hw' : w t ≤ T ^ κ * v t ^ κ := by
      simp only [hw]
      rw [← Real.mul_rpow hT0.le (hvpos t).le]
      exact Real.rpow_le_rpow (by positivity) hle hκ0
    have hdiv : w t / v t ≤ T ^ κ * v t ^ (κ - 1) := by
      rw [div_le_iff₀ (hvpos t), Real.rpow_sub (hvpos t), Real.rpow_one, mul_assoc,
        div_mul_cancel₀ _ (hvpos t).ne']
      exact hw'
    have h0 : 0 ≤ w t / v t := div_nonneg (by simp only [hw]; positivity) (hvpos t).le
    calc (w t / v t) ^ 2 ≤ (T ^ κ * v t ^ (κ - 1)) ^ 2 := pow_le_pow_left₀ h0 hdiv 2
      _ = T ^ (2 * κ) * v t ^ (2 * κ - 2) := by
          rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hT0.le,
            ← Real.rpow_mul (hvpos t).le]
          push_cast; ring_nf
  have hvInt : Integrable fun t => v t ^ (2 * κ - 2) := by
    have h := (integrable_one_add_abs_rpow (r := 2 * κ - 2) (by linarith)).comp_div hT0.ne'
    refine h.congr (Eventually.of_forall fun t => ?_)
    simp only [hv, abs_div, abs_of_pos hT0]
  have hvIntEq : ∫ t, v t ^ (2 * κ - 2) = T * Iκ := by
    simp only [hv]; rw [integral_one_add_abs_div_rpow hT0]; rfl
  -- the second factor
  have hvm : ∀ t, (v t * m t) ^ 2 ≤ 2 * m t ^ 2 + 2 / T ^ 2 * n t ^ 2 := by
    intro t
    have htm : |t| * m t ≤ n t := hf.abs_mul_norm_mellin_le σ t
    have hm0 : 0 ≤ m t := norm_nonneg _
    have h1 : (|t| / T * m t) ^ 2 ≤ n t ^ 2 / T ^ 2 := by
      rw [div_mul_eq_mul_div, div_pow]
      gcongr
    have : (v t * m t) ^ 2 ≤ 2 * m t ^ 2 + 2 * (|t| / T * m t) ^ 2 := by
      simp only [hv]; nlinarith [sq_nonneg (m t - |t| / T * m t)]
    calc (v t * m t) ^ 2 ≤ 2 * m t ^ 2 + 2 * (|t| / T * m t) ^ 2 := this
      _ ≤ 2 * m t ^ 2 + 2 * (n t ^ 2 / T ^ 2) := by gcongr
      _ = 2 * m t ^ 2 + 2 / T ^ 2 * n t ^ 2 := by ring
  -- AM-GM with a parameter
  set S : ℝ := B₀ + B₁ / T with hS
  have hS0 : 0 < S := by positivity
  set lam : ℝ := S / T ^ (κ + 1 / 2) with hlam
  have hlam0 : 0 < lam := by positivity
  have hpt : ∀ t, w t * m t ≤
      (lam * (T ^ (2 * κ) * v t ^ (2 * κ - 2)) +
        (2 * m t ^ 2 + 2 / T ^ 2 * n t ^ 2) / lam) / 2 := by
    intro t
    have hx := hwv t
    have hy := hvm t
    have hprod : w t * m t = (w t / v t) * (v t * m t) := by
      field_simp [(hvpos t).ne']
    rw [hprod]
    have amgm : (w t / v t) * (v t * m t) ≤
        (lam * (w t / v t) ^ 2 + (v t * m t) ^ 2 / lam) / 2 := by
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
      have : 0 ≤ (lam * (w t / v t) - v t * m t) ^ 2 / lam := by positivity
      have e : (lam * (w t / v t) - v t * m t) ^ 2 / lam =
          lam * (w t / v t) ^ 2 + (v t * m t) ^ 2 / lam - 2 * ((w t / v t) * (v t * m t)) := by
        field_simp; ring
      linarith
    refine amgm.trans ?_
    gcongr
  have hwmInt : Integrable fun t => w t * m t := hf.integrable_rpow_mul_norm_mellin σ (by linarith)
  have h1 : Integrable fun t => lam * (T ^ (2 * κ) * v t ^ (2 * κ - 2)) :=
    (hvInt.const_mul _).const_mul _
  have h3 : Integrable fun t => 2 * m t ^ 2 := hmInt.const_mul 2
  have h4 : Integrable fun t => 2 / T ^ 2 * n t ^ 2 := hnInt.const_mul _
  have h2 : Integrable fun t => (2 * m t ^ 2 + 2 / T ^ 2 * n t ^ 2) / lam :=
    (h3.add h4).div_const lam
  have hrhsInt : Integrable fun t => (lam * (T ^ (2 * κ) * v t ^ (2 * κ - 2)) +
      (2 * m t ^ 2 + 2 / T ^ 2 * n t ^ 2) / lam) / 2 := (h1.add h2).div_const 2
  have hint : ∫ t, w t * m t ≤ ∫ t, (lam * (T ^ (2 * κ) * v t ^ (2 * κ - 2)) +
      (2 * m t ^ 2 + 2 / T ^ 2 * n t ^ 2) / lam) / 2 :=
    integral_mono hwmInt hrhsInt hpt
  have hEq : ∫ t, (lam * (T ^ (2 * κ) * v t ^ (2 * κ - 2)) +
      (2 * m t ^ 2 + 2 / T ^ 2 * n t ^ 2) / lam) / 2 =
      (lam * (T ^ (2 * κ) * (T * Iκ)) +
        (2 * (∫ t, m t ^ 2) + 2 / T ^ 2 * ∫ t, n t ^ 2) / lam) / 2 := by
    rw [integral_div, integral_add h1 h2, integral_const_mul, integral_const_mul, hvIntEq,
      integral_div, integral_add h3 h4, integral_const_mul, integral_const_mul]
  rw [hEq] at hint
  -- arithmetic
  have hT2 : 0 < T ^ (κ + 1 / 2) := by positivity
  have hA : lam * (T ^ (2 * κ) * (T * Iκ)) = S * Iκ * T ^ (κ + 1 / 2) := by
    have e : T ^ (2 * κ) * T = T ^ (κ + 1 / 2) * T ^ (κ + 1 / 2) := by
      rw [← Real.rpow_add_one hT0.ne', ← Real.rpow_add hT0]; congr 1; ring
    calc lam * (T ^ (2 * κ) * (T * Iκ)) = S / T ^ (κ + 1 / 2) * ((T ^ (2 * κ) * T) * Iκ) := by
          rw [hlam]; ring
      _ = S / T ^ (κ + 1 / 2) * ((T ^ (κ + 1 / 2) * T ^ (κ + 1 / 2)) * Iκ) := by rw [e]
      _ = S * Iκ * T ^ (κ + 1 / 2) := by field_simp
  have hB : 2 * (∫ t, m t ^ 2) + 2 / T ^ 2 * ∫ t, n t ^ 2 ≤ 2 * c₀ * S ^ 2 := by
    have h1 : 2 / T ^ 2 * ∫ t, n t ^ 2 ≤ 2 / T ^ 2 * (c₀ * B₁ ^ 2) :=
      mul_le_mul_of_nonneg_left hQ (by positivity)
    have h2 : 2 * c₀ * B₀ ^ 2 + 2 / T ^ 2 * (c₀ * B₁ ^ 2) ≤ 2 * c₀ * S ^ 2 := by
      rw [hS]
      have : 2 / T ^ 2 * (c₀ * B₁ ^ 2) = 2 * c₀ * (B₁ / T) ^ 2 := by field_simp
      rw [this]
      have : 0 ≤ B₀ * (B₁ / T) := by positivity
      nlinarith
    linarith
  have hC : (2 * (∫ t, m t ^ 2) + 2 / T ^ 2 * ∫ t, n t ^ 2) / lam ≤
      2 * c₀ * S * T ^ (κ + 1 / 2) := by
    rw [div_le_iff₀ hlam0, hlam]
    calc 2 * (∫ t, m t ^ 2) + 2 / T ^ 2 * ∫ t, n t ^ 2 ≤ 2 * c₀ * S ^ 2 := hB
      _ = 2 * c₀ * S * T ^ (κ + 1 / 2) * (S / T ^ (κ + 1 / 2)) := by
          field_simp
  calc ∫ t : ℝ, (|t| + 1) ^ κ * ‖mellin f ((σ : ℂ) + t * I)‖ = ∫ t, w t * m t := rfl
    _ ≤ _ := hint
    _ ≤ (S * Iκ * T ^ (κ + 1 / 2) + 2 * c₀ * S * T ^ (κ + 1 / 2)) / 2 := by
        rw [hA]; gcongr
    _ = (Iκ + 2 * c₀) / 2 * (B₀ + B₁ / T) * T ^ (κ + 1 / 2) := by rw [hS]; ring

/-! ## Twisted test functions -/

/-- The twist `f_c(u) = F(u) e(c/u)`, `e(x) = exp(2πix)`. -/
def twist (F : ℝ → ℂ) (c : ℝ) (u : ℝ) : ℂ :=
  F u * Complex.exp (((2 * π * (c / u) : ℝ) : ℂ) * I)

theorem norm_twist (F : ℝ → ℂ) (c u : ℝ) : ‖twist F c u‖ = ‖F u‖ := by
  rw [twist, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]

/-- The phase `u ↦ e(c/u)` has derivative `−2πi c u^{−2} e(c/u)` for `u ≠ 0`. -/
theorem hasDerivAt_phase (c : ℝ) {u : ℝ} (hu : u ≠ 0) :
    HasDerivAt (fun u : ℝ => Complex.exp (((2 * π * (c / u) : ℝ) : ℂ) * I))
      (Complex.exp (((2 * π * (c / u) : ℝ) : ℂ) * I) *
        ((((-(2 * π * c)) / u ^ 2 : ℝ) : ℂ) * I)) u := by
  have h1 : HasDerivAt (fun u : ℝ => 2 * π * (c / u)) ((-(2 * π * c)) / u ^ 2) u := by
    have := (hasDerivAt_inv hu).const_mul (2 * π * c)
    have e1 : (fun u : ℝ => 2 * π * (c / u)) = fun y => 2 * π * c * y⁻¹ := by
      funext y; rw [div_eq_mul_inv]; ring
    rw [e1]; exact this.congr_deriv (by ring)
  exact (h1.ofReal_comp.mul_const I).cexp

variable {F : ℝ → ℂ}

theorem IsTest.twist_eventually_zero (hF : IsTest F a b) (c : ℝ) {u : ℝ} (hu : u < a) :
    twist F c =ᶠ[𝓝 u] fun _ => 0 := by
  filter_upwards [Iio_mem_nhds hu] with v hv
  simp [twist, hF.eq_zero_of_le (le_of_lt hv)]

/-- A twisted test function is a test function on the same interval. -/
theorem IsTest.twist (hF : IsTest F a b) (c : ℝ) : IsTest (twist F c) a b := by
  refine ⟨hF.pos, hF.le, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro u
    rcases lt_or_ge u a with hu | hu
    · exact contDiffAt_const.congr_of_eventuallyEq (hF.twist_eventually_zero c hu)
    · have hu0 : 0 < u := lt_of_lt_of_le hF.pos hu
      have h1 : ContDiffAt ℝ ∞ (fun u : ℝ => 2 * π * (c / u)) u :=
        contDiffAt_const.mul (contDiffAt_const.div contDiffAt_id hu0.ne')
      have h2 : ContDiffAt ℝ ∞ (fun u : ℝ => (((2 * π * (c / u) : ℝ) : ℂ) * I)) u :=
        (Complex.ofRealCLM.contDiff.contDiffAt.comp u h1).mul contDiffAt_const
      exact hF.smooth.contDiffAt.mul (Complex.contDiff_exp.contDiffAt.comp u h2)
  · intro u hu
    apply hF.supp
    intro h; apply hu; simp [GaloisForLFunctions.HTGeometry.TestFunctionPerron.twist, h]

/-- `|u f_c'(u)| ≤ |u F'|_∞ + 2π|c| |F|_∞/a`. -/
theorem norm_mul_deriv_twist_le (hF : IsTest F a b) {B₀ B₁ : ℝ} (hB₀ : ∀ u, ‖F u‖ ≤ B₀)
    (hB₁ : ∀ u : ℝ, ‖(u : ℂ) * deriv F u‖ ≤ B₁) (c u : ℝ) :
    ‖(u : ℂ) * deriv (twist F c) u‖ ≤ B₁ + 2 * π * |c| * B₀ / a := by
  have hB₁0 : 0 ≤ B₁ := (norm_nonneg _).trans (hB₁ 0)
  have hB₀0 : 0 ≤ B₀ := (norm_nonneg _).trans (hB₀ 0)
  have ha := hF.pos
  rcases lt_or_ge u a with hu | hu
  · rw [(hF.twist_eventually_zero c hu).deriv_eq]
    simp only [deriv_const', mul_zero, norm_zero]
    positivity
  · have hu0 : 0 < u := lt_of_lt_of_le ha hu
    have hdF : HasDerivAt F (deriv F u) u :=
      ((contDiff_infty_iff_deriv.mp hF.smooth).1 u).hasDerivAt
    set E : ℂ := Complex.exp (((2 * π * (c / u) : ℝ) : ℂ) * I) with hE
    have hd := hdF.mul (hasDerivAt_phase c hu0.ne')
    have hd' : deriv (twist F c) u =
        deriv F u * E + F u * (E * ((((-(2 * π * c)) / u ^ 2 : ℝ) : ℂ) * I)) := hd.deriv
    rw [hd']
    have hEn : ‖E‖ = 1 := Complex.norm_exp_ofReal_mul_I _
    have hrw : (u : ℂ) * (deriv F u * E + F u * (E * ((((-(2 * π * c)) / u ^ 2 : ℝ) : ℂ) * I))) =
        ((u : ℂ) * deriv F u) * E + F u * E * ((((-(2 * π * c)) / u : ℝ) : ℂ) * I) := by
      have hu' : (u : ℂ) ≠ 0 := by exact_mod_cast hu0.ne'
      push_cast
      field_simp
    rw [hrw]
    have hph : ‖((((-(2 * π * c)) / u : ℝ) : ℂ) * I)‖ ≤ 2 * π * |c| / a := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_div,
        abs_neg, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π), abs_of_pos hu0]
      gcongr
    calc ‖((u : ℂ) * deriv F u) * E + F u * E * ((((-(2 * π * c)) / u : ℝ) : ℂ) * I)‖
        ≤ ‖(u : ℂ) * deriv F u‖ * ‖E‖ + ‖F u‖ * ‖E‖ *
            ‖((((-(2 * π * c)) / u : ℝ) : ℂ) * I)‖ := by
          refine (norm_add_le _ _).trans (le_of_eq ?_)
          rw [norm_mul ((u : ℂ) * deriv F u) E, norm_mul (F u * E), norm_mul (F u) E]
      _ ≤ B₁ * 1 + B₀ * 1 * (2 * π * |c| / a) := by
          rw [hEn]
          gcongr
          · exact hB₁ u
          · exact hB₀ u
      _ = B₁ + 2 * π * |c| * B₀ / a := by ring

/-- **The oscillation bound.** `∫ (|t| + 1)^κ |𝓜f_c(σ + it)| dt ≪ (1 + |c|)^{κ + 1/2}`. -/
theorem exists_integral_twist_le (hF : IsTest F a b) {σ κ : ℝ} (hσ : 0 ≤ σ) (hκ0 : 0 ≤ κ)
    (hκ : κ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c : ℝ,
      ∫ t : ℝ, (|t| + 1) ^ κ * ‖mellin (twist F c) ((σ : ℂ) + t * I)‖ ≤
        C * (1 + |c|) ^ (κ + 1 / 2) := by
  have ha := hF.pos
  obtain ⟨C₀, hC₀0, hC₀⟩ := integral_rpow_mul_norm_mellin_le ha hF.le hσ hκ0 hκ
  obtain ⟨B₀', hB₀'0, hB₀'⟩ := hF.exists_bound
  obtain ⟨B₁, hB₁0, hB₁⟩ := hF.eulerDeriv.exists_bound
  set B₀ := B₀' + 1 with hB₀
  have hB₀le : ∀ u, ‖F u‖ ≤ B₀ := fun u => by linarith [hB₀' u]
  refine ⟨C₀ * (B₀ + B₁ + 2 * π * B₀ / a), by positivity, fun c => ?_⟩
  have hT : 1 ≤ 1 + |c| := by linarith [abs_nonneg c]
  have h := hC₀ (twist F c) (hF.twist c) B₀ (B₁ + 2 * π * |c| * B₀ / a) (1 + |c|)
    (by positivity) (by positivity) hT (fun u => by rw [norm_twist]; exact hB₀le u)
    (norm_mul_deriv_twist_le hF hB₀le hB₁ c)
  refine h.trans ?_
  have hpow : 0 ≤ (1 + |c|) ^ (κ + 1 / 2) := by positivity
  have hfrac : (B₁ + 2 * π * |c| * B₀ / a) / (1 + |c|) ≤ B₁ + 2 * π * B₀ / a := by
    rw [div_le_iff₀ (by positivity)]
    have : 0 ≤ |c| := abs_nonneg c
    have h2 : 0 ≤ 2 * π * B₀ / a := by positivity
    have e : 2 * π * |c| * B₀ / a = |c| * (2 * π * B₀ / a) := by ring
    rw [e]; nlinarith
  calc C₀ * (B₀ + (B₁ + 2 * π * |c| * B₀ / a) / (1 + |c|)) * (1 + |c|) ^ (κ + 1 / 2)
      ≤ C₀ * (B₀ + (B₁ + 2 * π * B₀ / a)) * (1 + |c|) ^ (κ + 1 / 2) := by gcongr
    _ = C₀ * (B₀ + B₁ + 2 * π * B₀ / a) * (1 + |c|) ^ (κ + 1 / 2) := by ring

/-- **The residue bound.**  At a real point `ρ`, `|𝓜f_c(ρ)| ≪ 1/(1 + |c|)`. -/
theorem exists_norm_mellin_twist_le (hF : IsTest F a b) (ρ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c : ℝ, ‖mellin (twist F c) (ρ : ℂ)‖ ≤ C / (1 + |c|) := by
  have ha := hF.pos
  have hab := hF.le
  have hb : 0 < b := lt_of_lt_of_le ha hab
  obtain ⟨B₀, hB₀0, hB₀⟩ := hF.exists_bound
  set C₁ := (b - a) * Real.exp (|ρ - 1| * IsTest.logScale a b) * B₀ with hC₁
  have hC₁0 : 0 ≤ C₁ := by
    have : 0 ≤ b - a := by linarith
    positivity
  have htriv : ∀ c : ℝ, ‖mellin (twist F c) (ρ : ℂ)‖ ≤ C₁ := fun c =>
    (hF.twist c).norm_mellin_le (fun u => by rw [norm_twist]; exact hB₀ u) (by simp)
  -- the derivative of `g(u) = u^{ρ+1} F(u)`
  have hdF : ∀ u, HasDerivAt F (deriv F u) u := fun u =>
    ((contDiff_infty_iff_deriv.mp hF.smooth).1 u).hasDerivAt
  have hcdF : Continuous (deriv F) := (contDiff_infty_iff_deriv.mp hF.smooth).2.continuous
  set g : ℝ → ℂ := fun u => ((u ^ (ρ + 1) : ℝ) : ℂ) * F u with hg
  set g' : ℝ → ℂ := fun u => (((ρ + 1) * u ^ ρ : ℝ) : ℂ) * F u + ((u ^ (ρ + 1) : ℝ) : ℂ) * deriv F u
    with hg'
  have hpos : ∀ u ∈ [[a, b]], 0 < u := fun u hu => by
    rw [Set.uIcc_of_le hab] at hu; exact lt_of_lt_of_le ha hu.1
  have hgd : ∀ u ∈ [[a, b]], HasDerivAt g (g' u) u := by
    intro u hu
    have hu0 := hpos u hu
    have h1 : HasDerivAt (fun u : ℝ => u ^ (ρ + 1)) ((ρ + 1) * u ^ (ρ + 1 - 1)) u :=
      Real.hasDerivAt_rpow_const (Or.inl hu0.ne')
    rw [show ρ + 1 - 1 = ρ by ring] at h1
    exact h1.ofReal_comp.mul (hdF u)
  have hg'c : ContinuousOn g' [[a, b]] := by
    intro u hu
    have hu0 := hpos u hu
    have hr1 : ContinuousAt (fun u : ℝ => u ^ ρ) u :=
      Real.continuousAt_rpow_const _ _ (Or.inl hu0.ne')
    have hr2 : ContinuousAt (fun u : ℝ => u ^ (ρ + 1)) u :=
      Real.continuousAt_rpow_const _ _ (Or.inl hu0.ne')
    refine ContinuousAt.continuousWithinAt ?_
    simp only [hg']
    refine ContinuousAt.add ?_ ?_
    · exact (Complex.continuous_ofReal.continuousAt.comp (continuousAt_const.mul hr1)).mul
        hF.continuous.continuousAt
    · exact (Complex.continuous_ofReal.continuousAt.comp hr2).mul hcdF.continuousAt
  obtain ⟨G, hG⟩ := (isCompact_uIcc (a := a) (b := b)).exists_bound_of_continuousOn hg'c
  have hG0 : 0 ≤ G := (norm_nonneg _).trans (hG a Set.left_mem_uIcc)
  set C₂ := G * (b - a) / (2 * π) with hC₂
  have hC₂0 : 0 ≤ C₂ := by
    have : 0 ≤ b - a := by linarith
    positivity
  have hibp : ∀ c : ℝ, |c| * ‖mellin (twist F c) (ρ : ℂ)‖ ≤ C₂ := by
    intro c
    rcases eq_or_ne c 0 with rfl | hc
    · simp; exact hC₂0
    set E : ℝ → ℂ := fun u => Complex.exp (((2 * π * (c / u) : ℝ) : ℂ) * I) with hE
    set E' : ℝ → ℂ := fun u => E u * ((((-(2 * π * c)) / u ^ 2 : ℝ) : ℂ) * I) with hE'
    have hEd : ∀ u ∈ [[a, b]], HasDerivAt E (E' u) u := fun u hu =>
      hasDerivAt_phase c (hpos u hu).ne'
    have hE'c : ContinuousOn E' [[a, b]] := by
      intro u hu
      have hu0 := hpos u hu
      refine ContinuousAt.continuousWithinAt ?_
      have h1 : ContinuousAt (fun u : ℝ => 2 * π * (c / u)) u :=
        continuousAt_const.mul (continuousAt_const.div continuousAt_id hu0.ne')
      have h2 : ContinuousAt (fun u : ℝ => (-(2 * π * c)) / u ^ 2) u :=
        continuousAt_const.div (continuousAt_id.pow 2) (pow_ne_zero 2 hu0.ne')
      exact (Complex.continuous_exp.continuousAt.comp
        ((Complex.continuous_ofReal.continuousAt.comp h1).mul continuousAt_const)).mul
        ((Complex.continuous_ofReal.continuousAt.comp h2).mul continuousAt_const)
    have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul hgd hEd
      (hg'c.intervalIntegrable) (hE'c.intervalIntegrable)
    have hga : g a = 0 := by simp [hg, hF.eq_zero_of_le le_rfl]
    have hgb : g b = 0 := by simp [hg, hF.eq_zero_of_ge le_rfl]
    rw [hga, hgb, zero_mul, zero_mul, sub_zero, zero_sub] at hparts
    -- the Mellin integrand is a multiple of `g E'`
    have hkey : ∀ u ∈ [[a, b]], g u * E' u =
        (((-(2 * π * c)) : ℝ) : ℂ) * I * ((u : ℂ) ^ ((ρ : ℂ) - 1) * twist F c u) := by
      intro u hu
      have hu0 := hpos u hu
      have hcpow : (u : ℂ) ^ ((ρ : ℂ) - 1) = ((u ^ (ρ - 1) : ℝ) : ℂ) := by
        rw [Complex.ofReal_cpow hu0.le]; push_cast; ring_nf
      have hrp : u ^ (ρ + 1) / u ^ 2 = u ^ (ρ - 1) := by
        rw [← Real.rpow_natCast, ← Real.rpow_sub hu0]; norm_num; ring_nf
      rw [hcpow]
      simp only [hg, hE', hE, twist]
      have hu2 : (u : ℂ) ^ 2 ≠ 0 := by exact_mod_cast pow_ne_zero 2 hu0.ne'
      rw [← hrp]
      push_cast
      field_simp
    have hmel : mellin (twist F c) (ρ : ℂ) =
        ∫ u in a..b, (u : ℂ) ^ ((ρ : ℂ) - 1) * twist F c u := (hF.twist c).mellin_eq _
    have hint : ∫ u in a..b, g u * E' u =
        (((-(2 * π * c)) : ℝ) : ℂ) * I * mellin (twist F c) (ρ : ℂ) := by
      rw [hmel, ← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_congr hkey
    rw [hint] at hparts
    have hbound : ‖∫ u in a..b, g' u * E u‖ ≤ G * (b - a) := by
      refine (intervalIntegral.norm_integral_le_of_norm_le_const fun u hu => ?_).trans
        (le_of_eq (by rw [abs_of_nonneg (by linarith)]))
      have hu' : u ∈ [[a, b]] := Set.uIoc_subset_uIcc hu
      rw [norm_mul, hE]
      simp only [Complex.norm_exp_ofReal_mul_I, mul_one]
      exact hG u hu'
    have hnorm : ‖(((-(2 * π * c)) : ℝ) : ℂ) * I * mellin (twist F c) (ρ : ℂ)‖ =
        2 * π * |c| * ‖mellin (twist F c) (ρ : ℂ)‖ := by
      rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_neg, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
    have hn := congrArg norm hparts
    rw [norm_neg, hnorm] at hn
    rw [← hn] at hbound
    rw [hC₂, le_div_iff₀ (by positivity)]
    linarith
  refine ⟨C₁ + C₂, by positivity, fun c => ?_⟩
  rw [le_div_iff₀ (by positivity)]
  have h1 := htriv c
  have h2 := hibp c
  nlinarith [norm_nonneg (mellin (twist F c) (ρ : ℂ))]

end GaloisForLFunctions.HTGeometry.TestFunctionPerron
