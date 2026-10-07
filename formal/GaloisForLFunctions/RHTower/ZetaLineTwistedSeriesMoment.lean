import GaloisForLFunctions.RHTower.ZetaTwistedFirstMomentContour
import GaloisForLFunctions.RHTower.WeilConeBoundaryDilationRigidity

/-!
# Twisted first moments of `F ζ̄` on the critical line

Let `F(s) = Σ f(n) n^{−s}` with `Σ |f(n)| n^{−½}(1 + log n) < ∞`, and let `h, k ≥ 1`. Then

`(1/T) ∫_T^{2T} (h/k)^{it} F(½+it) conj ζ(½+it) dt → Σ_{h ∣ kn} f(n) √h/(√k · n)`

(`tendsto_twistMean`).

**Proof.** For a single term `n`, `(h/k)^{it} n^{−½−it} conj ζ(½+it)` is the conjugate of the first
moment of `ζ` twisted by `kn/h`. That moment is `[h ∣ kn] (h/kn)^{½} T + O(√(hkn)(√T kn + (kn)²))`
(`norm_integral_twistedZeta_sub_diag_le`). Truncate `F` at
`N = ⌊T^{1/8}⌋`. The head carries the main terms with error `O(T^{1−5/16})`. The tail is bounded by
`τ_N ∫_T^{2T} |ζ|`, where `τ_N = Σ_{n>N} |f(n)| n^{−½}`. The mean square gives
`∫_T^{2T} |ζ| = O(T log T)`, and the log moment gives `τ_N = o(1/log N)`.
-/

noncomputable section

open Complex Filter Topology Set MeasureTheory

namespace RHTower.ZetaLineTwist

open RHTower.WeilBoundaryDilation

local notation "eχ" => _root_.GaloisForLFunctions.expChar

/-! ## One twisted integral of `ζ` -/

theorem sqrt_mul_eq_exp {d m : ℕ} (hd : 1 ≤ d) (hm : 1 ≤ m) :
    Real.sqrt ((d : ℝ) * m) = Real.exp ((Real.log d + Real.log m) / 2) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (mul_pos hd0 hm0), Real.log_mul hd0.ne' hm0.ne']
  ring_nf

/-- `ζ(½+it) (m/d)^{it} = √(dm) · g(½+it)`, `g` the twisted zeta of the contour module. -/
theorem zeta_mul_expChar_eq {d m : ℕ} (hd : 1 ≤ d) (hm : 1 ≤ m) (t : ℝ) :
    riemannZeta (linePt t) * eχ (Real.log m - Real.log d) t =
      (Real.sqrt ((d : ℝ) * m) : ℂ) *
        twistedZeta (1 / 2) d m (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) := by
  unfold twistedZeta
  rw [ofReal_half_add_eq_linePt, ofReal_natCast_cpow_eq_exp hd, ofReal_natCast_cpow_eq_exp hm,
    sqrt_mul_eq_exp hd hm]
  unfold _root_.GaloisForLFunctions.expChar
  rw [Complex.ofReal_exp]
  have e : riemannZeta (linePt t) *
      (Complex.exp (((Real.log d + Real.log m) / 2 : ℝ) : ℂ) *
        (Complex.exp ((Real.log d : ℂ) * -linePt t) *
          Complex.exp ((Real.log m : ℂ) * (linePt t - 2 * ((1 / 2 : ℝ) : ℂ))))) =
      riemannZeta (linePt t) * Complex.exp (((Real.log d + Real.log m) / 2 : ℝ) +
        (Real.log d : ℂ) * -linePt t + (Real.log m : ℂ) * (linePt t - 2 * ((1 / 2 : ℝ) : ℂ))) := by
    rw [Complex.exp_add, Complex.exp_add]; ring
  rw [show (Complex.exp (((Real.log d + Real.log m) / 2 : ℝ) : ℂ) *
      (riemannZeta (linePt t) * Complex.exp ((Real.log d : ℂ) * -linePt t) *
        Complex.exp ((Real.log m : ℂ) * (linePt t - 2 * ((1 / 2 : ℝ) : ℂ))))) =
      riemannZeta (linePt t) *
      (Complex.exp (((Real.log d + Real.log m) / 2 : ℝ) : ℂ) *
        (Complex.exp ((Real.log d : ℂ) * -linePt t) *
          Complex.exp ((Real.log m : ℂ) * (linePt t - 2 * ((1 / 2 : ℝ) : ℂ))))) by ring, e]
  congr 2
  unfold linePt
  push_cast
  ring

theorem continuous_zeta_linePt : Continuous fun t : ℝ => riemannZeta (linePt t) := by
  refine continuous_iff_continuousAt.mpr fun t => ?_
  exact ((analyticOn_riemannZeta (linePt t) (linePt_ne_one t)).continuousAt).comp
    continuous_linePt.continuousAt

/-- **The twisted first moment of `ζ`**:
`‖∫_T^{2T} ζ(½+it)(m/d)^{it} dt − [d ∣ m] √(d/m) T‖ ≤ √(dm)(27√T m + 8m²)`. -/
theorem norm_integral_zeta_expChar_sub_le {d m : ℕ} (hd : 1 ≤ d) (hm : 1 ≤ m) {T : ℝ}
    (hT : 4 ≤ T) :
    ‖(∫ t in T..(2 * T), riemannZeta (linePt t) * eχ (Real.log m - Real.log d) t) -
        (if d ∣ m then ((Real.sqrt d / Real.sqrt m * T : ℝ) : ℂ) else 0)‖ ≤
      Real.sqrt ((d : ℝ) * m) * (27 * Real.sqrt T * m + 8 * (m : ℝ) ^ 2) := by
  have h := norm_integral_twistedZeta_sub_diag_le (σ := 1 / 2) (by norm_num) (by norm_num) hd hm hT
  have hint : ∫ t in T..(2 * T), riemannZeta (linePt t) * eχ (Real.log m - Real.log d) t =
      (Real.sqrt ((d : ℝ) * m) : ℂ) *
        ∫ t in T..(2 * T), twistedZeta (1 / 2) d m (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun t _ => zeta_mul_expChar_eq hd hm t
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hdiag : (if d ∣ m then ((Real.sqrt d / Real.sqrt m * T : ℝ) : ℂ) else 0) =
      (Real.sqrt ((d : ℝ) * m) : ℂ) *
        (if d ∣ m then (((m : ℝ) ^ (-2 * (1 / 2 : ℝ)) * T : ℝ) : ℂ) else 0) := by
    split_ifs
    · rw [← Complex.ofReal_mul]
      congr 1
      have hsq : Real.sqrt m * Real.sqrt m = m := Real.mul_self_sqrt hm0.le
      rw [show (-2 * (1 / 2 : ℝ)) = -1 by norm_num, Real.rpow_neg_one, Real.sqrt_mul hd0.le]
      field_simp
      nlinarith [Real.sqrt_nonneg (m : ℝ)]
    · simp
  rw [hint, hdiag, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  exact mul_le_mul_of_nonneg_left h (Real.sqrt_nonneg _)

theorem integral_conj_eq {g : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b) :
    ∫ t in a..b, (starRingEnd ℂ) (g t) = (starRingEnd ℂ) (∫ t in a..b, g t) := by
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
  exact integral_conj

/-! ## One term of `F ζ̄` -/

/-- **The twisted first moment of one term of `F ζ̄`.** For `h, k, n ≥ 1`, the integral of
`(h/k)^{it} n^{−it} conj ζ(½+it)` over `[T, 2T]` is `[h ∣ kn] √h/√(kn) · T` up to
`√(hkn)(27√T kn + 8(kn)²)`. -/
theorem norm_integral_twist_term_sub_le {h k n : ℕ} (hh : 1 ≤ h) (hk : 1 ≤ k) (hn : 1 ≤ n)
    {T : ℝ} (hT : 4 ≤ T) :
    ‖(∫ t in T..(2 * T), eχ (Real.log h - Real.log k) t *
        (eχ (-Real.log n) t * (starRingEnd ℂ) (riemannZeta (linePt t)))) -
      (if h ∣ k * n then ((Real.sqrt h / Real.sqrt ((k * n : ℕ) : ℝ) * T : ℝ) : ℂ) else 0)‖ ≤
      Real.sqrt ((h : ℝ) * (k * n : ℕ)) *
        (27 * Real.sqrt T * (k * n : ℕ) + 8 * ((k * n : ℕ) : ℝ) ^ 2) := by
  have hkn : 1 ≤ k * n := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have h1 := norm_integral_zeta_expChar_sub_le hh hkn hT
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hc : Real.log h - Real.log k + -Real.log n = -(Real.log (k * n : ℕ) - Real.log h) := by
    push_cast
    rw [Real.log_mul hk0.ne' hn0.ne']
    ring
  have hint : ∫ t in T..(2 * T), eχ (Real.log h - Real.log k) t *
        (eχ (-Real.log n) t * (starRingEnd ℂ) (riemannZeta (linePt t))) =
      (starRingEnd ℂ) (∫ t in T..(2 * T),
        riemannZeta (linePt t) * eχ (Real.log (k * n : ℕ) - Real.log h) t) := by
    rw [← integral_conj_eq (by linarith)]
    refine intervalIntegral.integral_congr fun t _ => ?_
    calc eχ (Real.log h - Real.log k) t *
          (eχ (-Real.log n) t * (starRingEnd ℂ) (riemannZeta (linePt t)))
        = (eχ (Real.log h - Real.log k) t * eχ (-Real.log n) t) *
            (starRingEnd ℂ) (riemannZeta (linePt t)) := by ring
      _ = eχ (Real.log h - Real.log k + -Real.log n) t *
            (starRingEnd ℂ) (riemannZeta (linePt t)) := by
          rw [_root_.GaloisForLFunctions.expChar_add]
      _ = (starRingEnd ℂ) (riemannZeta (linePt t)) *
            eχ (-(Real.log (k * n : ℕ) - Real.log h)) t := by rw [hc]; ring
      _ = (starRingEnd ℂ) (riemannZeta (linePt t) *
            eχ (Real.log (k * n : ℕ) - Real.log h) t) := by
          rw [map_mul, _root_.GaloisForLFunctions.conj_expChar]
  have hmain : (if h ∣ k * n then ((Real.sqrt h / Real.sqrt ((k * n : ℕ) : ℝ) * T : ℝ) : ℂ)
      else 0) = (starRingEnd ℂ) (if h ∣ k * n then
        ((Real.sqrt h / Real.sqrt ((k * n : ℕ) : ℝ) * T : ℝ) : ℂ) else 0) := by
    split_ifs <;> simp
  rw [hint, hmain, ← map_sub, Complex.norm_conj]
  exact h1

/-! ## Bounds for the averaging -/

/-- The coefficient `f(n) n^{−½}`. -/
abbrev coef (f : ℕ → ℂ) (n : ℕ) : ℂ := LSeries.term f (1 / 2) n

variable {f : ℕ → ℂ}

theorem LSeries_linePt_eq_tsum (t : ℝ) :
    LSeries f (linePt t) = ∑' n, coef f n * eχ (-Real.log n) t := by
  unfold LSeries
  exact tsum_congr fun n => term_linePt_eq f n t

theorem norm_coef_mul (n : ℕ) (t : ℝ) : ‖coef f n * eχ (-Real.log n) t‖ = ‖coef f n‖ := by
  rw [norm_mul, _root_.GaloisForLFunctions.norm_expChar, mul_one]

theorem norm_logCoef (n : ℕ) :
    ‖LSeries.term (LSeries.logMul f) (1 / 2) n‖ = Real.log n * ‖coef f n‖ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hl : ‖Complex.log (n : ℂ)‖ = Real.log n := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg n), Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg (by exact_mod_cast hn))]
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq, if_neg hn.ne', if_neg hn.ne', LSeries.logMul,
      norm_mul, hl, mul_div_assoc]

/-- **First absolute moment on `[T, 2T]`**: `∫_T^{2T} |ζ(½+it)| ≤ C T (3 + log T)`. -/
theorem exists_integral_norm_zeta_line_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {T : ℝ}, 4 ≤ T →
      ∫ t in T..(2 * T), ‖riemannZeta (linePt t)‖ ≤ C * T * (3 + Real.log T) := by
  obtain ⟨D, hD, hms⟩ := exists_integral_hardyZ_sq_le
  refine ⟨1 + 3 * D, by positivity, fun {T} hT => ?_⟩
  have hT0 : 0 < T := by linarith
  set lam := 1 + Real.log (2 * T + 1) with hlam
  have hlog1 : 0 ≤ Real.log (2 * T + 1) := Real.log_nonneg (by linarith)
  have hlam0 : 0 < lam := by linarith
  have hlamle : lam ≤ 3 + Real.log T := by
    have h3 : Real.log (2 * T + 1) ≤ Real.log (3 * T) := Real.log_le_log (by linarith) (by linarith)
    rw [Real.log_mul (by norm_num) hT0.ne'] at h3
    have hl3 : Real.log 3 < 2 := by
      have := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 3) (by norm_num)
      linarith
    linarith
  have hpt : ∀ t ∈ Set.Icc T (2 * T), ‖riemannZeta (linePt t)‖ ≤
      lam / 2 + hardyZ t ^ 2 / (2 * lam) := by
    intro t _
    rw [norm_riemannZeta_linePt]
    have h := sq_nonneg (|hardyZ t| - lam)
    have hsq : |hardyZ t| ^ 2 = hardyZ t ^ 2 := sq_abs _
    rw [div_add_div _ _ (by norm_num) (by positivity), le_div_iff₀ (by positivity)]
    nlinarith
  have hcz : Continuous fun t => ‖riemannZeta (linePt t)‖ := continuous_zeta_linePt.norm
  have hZc : Continuous fun t => hardyZ t ^ 2 := differentiable_hardyZ.continuous.pow 2
  have hm : ∫ t in T..(2 * T), ‖riemannZeta (linePt t)‖ ≤
      ∫ t in T..(2 * T), (lam / 2 + hardyZ t ^ 2 / (2 * lam)) :=
    intervalIntegral.integral_mono_on (by linarith) (hcz.intervalIntegrable _ _)
      ((continuous_const.add (hZc.div_const _)).intervalIntegrable T (2 * T)) hpt
  have hZi : IntervalIntegrable (fun t => hardyZ t ^ 2 / (2 * lam)) volume T (2 * T) :=
    (hZc.div_const _).intervalIntegrable _ _
  rw [intervalIntegral.integral_add intervalIntegrable_const hZi,
    intervalIntegral.integral_const, intervalIntegral.integral_div, smul_eq_mul] at hm
  have hZ := hms (T₁ := T) (T₂ := 2 * T) hT0.le (by linarith) (by linarith)
  have hZ' : (∫ t in T..(2 * T), hardyZ t ^ 2) / (2 * lam) ≤ D * (2 * T + 1) * lam / 2 := by
    rw [div_le_iff₀ (by positivity)]
    have : D * (2 * T + 1) * (1 + Real.log (2 * T + 1)) ^ 2 = D * (2 * T + 1) * lam * lam := by
      rw [hlam]; ring
    nlinarith
  have hfin : (2 * T - T) * (lam / 2) + D * (2 * T + 1) * lam / 2 ≤ (1 + 3 * D) * T * lam := by
    have hs : T / 2 + D * T + D / 2 ≤ T + 3 * D * T := by nlinarith
    calc (2 * T - T) * (lam / 2) + D * (2 * T + 1) * lam / 2 = lam * (T / 2 + D * T + D / 2) := by
          ring
      _ ≤ lam * (T + 3 * D * T) := mul_le_mul_of_nonneg_left hs hlam0.le
      _ = (1 + 3 * D) * T * lam := by ring
  calc ∫ t in T..(2 * T), ‖riemannZeta (linePt t)‖ ≤ (1 + 3 * D) * T * lam := by linarith
    _ ≤ (1 + 3 * D) * T * (3 + Real.log T) := by
      apply mul_le_mul_of_nonneg_left hlamle; positivity

/-! ## The twisted mean -/

/-- The diagonal weight `[h ∣ kn] √h/√(kn)`. -/
def diagWeight (h k n : ℕ) : ℝ :=
  if h ∣ k * n then Real.sqrt h / Real.sqrt ((k * n : ℕ) : ℝ) else 0

/-- The limit of the twisted mean: `Σ_n f(n) n^{−½} [h ∣ kn] √h/√(kn)`. -/
def twistValue (f : ℕ → ℂ) (h k : ℕ) : ℂ := ∑' n, coef f n * (diagWeight h k n : ℂ)

theorem abs_diagWeight_le {h k : ℕ} (hk : 1 ≤ k) (n : ℕ) : |diagWeight h k n| ≤ Real.sqrt h := by
  unfold diagWeight
  split_ifs
  · rw [abs_of_nonneg (by positivity)]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have h1 : (1 : ℝ) ≤ Real.sqrt ((k * n : ℕ) : ℝ) := by
        rw [Real.one_le_sqrt]
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
      exact div_le_self (Real.sqrt_nonneg _) h1
  · simp [Real.sqrt_nonneg]

/-- The tail `τ_M = Σ_{n ≥ M} |f(n)| n^{−½}`. -/
def tailMass (f : ℕ → ℂ) (M : ℕ) : ℝ := ∑' n, ‖coef f (n + M)‖

/-- The log-weighted tail `σ_M = Σ_{n ≥ M} |f(n)| n^{−½} log n`. -/
def logTailMass (f : ℕ → ℂ) (M : ℕ) : ℝ := ∑' n, Real.log ((n + M : ℕ) : ℝ) * ‖coef f (n + M)‖

theorem tailMass_le_logTailMass (hf : LSeriesSummable f (1 / 2))
    (hlog : LSeriesSummable (LSeries.logMul f) (1 / 2)) {M : ℕ} (hM : 2 ≤ M) :
    tailMass f M * Real.log M ≤ logTailMass f M := by
  have hs : Summable fun n => ‖coef f n‖ := summable_norm_iff.mpr hf
  have hsl : Summable fun n : ℕ => Real.log (n : ℝ) * ‖coef f n‖ :=
    (summable_norm_iff.mpr hlog).congr fun n => norm_logCoef n
  unfold tailMass logTailMass
  rw [← tsum_mul_right]
  refine Summable.tsum_le_tsum (fun n => ?_) ((summable_nat_add_iff M).mpr hs |>.mul_right _)
    ((summable_nat_add_iff M).mpr hsl)
  rw [mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  exact Real.log_le_log (by exact_mod_cast (by omega : 0 < M)) (by push_cast; linarith)

theorem tendsto_tailMass : Tendsto (tailMass f) atTop (𝓝 0) :=
  tendsto_sum_nat_add fun n => ‖coef f n‖

theorem tendsto_logTailMass : Tendsto (logTailMass f) atTop (𝓝 0) := by
  have h := tendsto_sum_nat_add fun n : ℕ => Real.log (n : ℝ) * ‖coef f n‖
  refine h.congr fun M => ?_
  unfold logTailMass
  push_cast
  rfl

/-- The truncation length `N(T) = ⌊T^{1/8}⌋`. -/
def cut (T : ℝ) : ℕ := ⌊T ^ ((1 : ℝ) / 8)⌋₊

theorem tendsto_cut : Tendsto cut atTop atTop :=
  tendsto_nat_floor_atTop.comp (tendsto_rpow_atTop (by norm_num))

theorem cut_pow_le {T : ℝ} (hT : 0 ≤ T) : ((cut T : ℕ) : ℝ) ^ 8 ≤ T := by
  have h := Nat.floor_le (Real.rpow_nonneg hT ((1 : ℝ) / 8))
  have h8 : (T ^ ((1 : ℝ) / 8)) ^ (8 : ℕ) = T := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hT]; norm_num
  calc ((cut T : ℕ) : ℝ) ^ 8 ≤ (T ^ ((1 : ℝ) / 8)) ^ (8 : ℕ) :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) h 8
    _ = T := h8

theorem log_cut_ge {T : ℝ} (hT : 1 ≤ T) : Real.log T / 8 ≤ Real.log ((cut T + 1 : ℕ) : ℝ) := by
  have hT0 : 0 < T := by linarith
  have h := Nat.lt_floor_add_one (T ^ ((1 : ℝ) / 8))
  have hpos : 0 < T ^ ((1 : ℝ) / 8) := Real.rpow_pos_of_pos hT0 _
  have hl : Real.log (T ^ ((1 : ℝ) / 8)) = Real.log T / 8 := by
    rw [Real.log_rpow hT0]; ring
  rw [← hl]
  exact Real.log_le_log hpos (by push_cast; unfold cut; linarith)

/-- The per-term error after normalization by `T`, for `1 ≤ n ≤ N` and `T ≥ N⁸`. -/
theorem twist_term_error_le {h k n N : ℕ} (hk : 1 ≤ k) (hn : 1 ≤ n) (hnN : n ≤ N) {T : ℝ}
    (hT : 4 ≤ T) (hNT : (N : ℝ) ^ 8 ≤ T) :
    T⁻¹ * (Real.sqrt ((h : ℝ) * (k * n : ℕ)) *
        (27 * Real.sqrt T * (k * n : ℕ) + 8 * ((k * n : ℕ) : ℝ) ^ 2)) ≤
      Real.sqrt ((h : ℝ) * k) * (27 * k + 8 * (k : ℝ) ^ 2) / N := by
  have hT0 : 0 < T := by linarith
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (le_trans hn hnN)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnN' : (n : ℝ) ≤ N := by exact_mod_cast hnN
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hsqT : (N : ℝ) ^ 4 ≤ Real.sqrt T := by
    rw [show (N : ℝ) ^ 4 = Real.sqrt (((N : ℝ) ^ 4) ^ 2) by rw [Real.sqrt_sq (by positivity)]]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hsqrtn : Real.sqrt ((h : ℝ) * (k * n : ℕ)) ≤ Real.sqrt ((h : ℝ) * k) * N := by
    have e : (h : ℝ) * (k * n : ℕ) = ((h : ℝ) * k) * n := by push_cast; ring
    rw [e, Real.sqrt_mul (by positivity)]
    gcongr
    calc Real.sqrt (n : ℝ) ≤ n := by
          rw [Real.sqrt_le_left (by positivity)]; nlinarith
      _ ≤ N := hnN'
  have hkn : ((k * n : ℕ) : ℝ) ≤ k * N := by push_cast; gcongr
  have hT8 : (N : ℝ) ^ 8 ≤ T := hNT
  have hb1 : 27 * Real.sqrt T * ((k * n : ℕ) : ℝ) / T ≤ 27 * k / N ^ 3 := by
    rw [div_le_div_iff₀ hT0 (by positivity)]
    have hsT : Real.sqrt T * Real.sqrt T = T := Real.mul_self_sqrt hT0.le
    have hpos : 0 ≤ Real.sqrt T := Real.sqrt_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left hkn (by positivity : (0 : ℝ) ≤ 27 * Real.sqrt T * N ^ 3),
      mul_le_mul_of_nonneg_left hsqT (by positivity : (0 : ℝ) ≤ 27 * k * Real.sqrt T)]
  have hb2 : 8 * ((k * n : ℕ) : ℝ) ^ 2 / T ≤ 8 * (k : ℝ) ^ 2 / N ^ 3 := by
    rw [div_le_div_iff₀ hT0 (by positivity)]
    have hkn2 : ((k * n : ℕ) : ℝ) ^ 2 ≤ (k * N) ^ 2 := pow_le_pow_left₀ (by positivity) hkn 2
    have hN5 : (N : ℝ) ^ 5 ≤ N ^ 8 := pow_le_pow_right₀ hN1 (by norm_num)
    nlinarith [mul_le_mul_of_nonneg_left hkn2 (by positivity : (0 : ℝ) ≤ 8 * N ^ 3),
      mul_le_mul_of_nonneg_left (hN5.trans hT8) (by positivity : (0 : ℝ) ≤ 8 * k ^ 2)]
  have hsum : T⁻¹ * (27 * Real.sqrt T * (k * n : ℕ) + 8 * ((k * n : ℕ) : ℝ) ^ 2) ≤
      (27 * k + 8 * (k : ℝ) ^ 2) / N ^ 3 := by
    rw [inv_mul_eq_div, add_div]
    calc _ ≤ 27 * k / N ^ 3 + 8 * (k : ℝ) ^ 2 / N ^ 3 := add_le_add hb1 hb2
      _ = _ := by ring
  have hN3 : (N : ℝ) ^ 3 ≥ N ^ 2 := pow_le_pow_right₀ hN1 (by norm_num)
  calc T⁻¹ * (Real.sqrt ((h : ℝ) * (k * n : ℕ)) *
        (27 * Real.sqrt T * (k * n : ℕ) + 8 * ((k * n : ℕ) : ℝ) ^ 2))
      = Real.sqrt ((h : ℝ) * (k * n : ℕ)) *
        (T⁻¹ * (27 * Real.sqrt T * (k * n : ℕ) + 8 * ((k * n : ℕ) : ℝ) ^ 2)) := by ring
    _ ≤ (Real.sqrt ((h : ℝ) * k) * N) * ((27 * k + 8 * (k : ℝ) ^ 2) / N ^ 3) :=
        mul_le_mul hsqrtn hsum (by positivity) (by positivity)
    _ ≤ Real.sqrt ((h : ℝ) * k) * (27 * k + 8 * (k : ℝ) ^ 2) / N := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        have hinv : (N : ℝ) * ((N : ℝ) ^ 3)⁻¹ ≤ (N : ℝ)⁻¹ := by
          rw [show (N : ℝ) * ((N : ℝ) ^ 3)⁻¹ = ((N : ℝ) ^ 2)⁻¹ by field_simp]
          exact inv_anti₀ (by positivity) (by nlinarith)
        have h0 : 0 ≤ Real.sqrt ((h : ℝ) * k) * (27 * k + 8 * (k : ℝ) ^ 2) := by positivity
        calc Real.sqrt ((h : ℝ) * k) * N * ((27 * k + 8 * (k : ℝ) ^ 2) * ((N : ℝ) ^ 3)⁻¹)
            = Real.sqrt ((h : ℝ) * k) * (27 * k + 8 * (k : ℝ) ^ 2) * (N * ((N : ℝ) ^ 3)⁻¹) := by
              ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hinv h0

/-- **The twisted mean at a fixed height.** -/
theorem norm_twistMean_sub_le (hf : LSeriesSummable f (1 / 2))
    (hlog : LSeriesSummable (LSeries.logMul f) (1 / 2)) {h k : ℕ} (hh : 1 ≤ h) (hk : 1 ≤ k)
    {C : ℝ}
    (hζ : ∀ {T : ℝ}, 4 ≤ T → ∫ t in T..(2 * T), ‖riemannZeta (linePt t)‖ ≤ C * T * (3 + Real.log T))
    {T : ℝ} (hT : 4 ≤ T) (hlT : 3 ≤ Real.log T) (hN : 1 ≤ cut T) :
    ‖T⁻¹ * (∫ t in T..(2 * T), eχ (Real.log h - Real.log k) t *
        (LSeries f (linePt t) * (starRingEnd ℂ) (riemannZeta (linePt t)))) - twistValue f h k‖ ≤
      (∑' n, ‖coef f n‖) * (Real.sqrt ((h : ℝ) * k) * (27 * k + 8 * (k : ℝ) ^ 2)) / cut T +
      Real.sqrt h * tailMass f (cut T + 1) + C * 16 * logTailMass f (cut T + 1) := by
  obtain ⟨N, hNdef⟩ : ∃ N, N = cut T := ⟨_, rfl⟩
  rw [← hNdef] at hN ⊢
  obtain ⟨M, hMdef⟩ : ∃ M, M = N + 1 := ⟨_, rfl⟩
  rw [← hMdef]
  obtain ⟨a, hadef⟩ : ∃ a, a = Real.log h - Real.log k := ⟨_, rfl⟩
  rw [← hadef]
  obtain ⟨K₀, hK₀⟩ : ∃ K₀, K₀ = Real.sqrt ((h : ℝ) * k) * (27 * k + 8 * (k : ℝ) ^ 2) := ⟨_, rfl⟩
  rw [← hK₀]
  have hT0 : 0 < T := by linarith
  have hs : Summable fun n => ‖coef f n‖ := summable_norm_iff.mpr hf
  have hst : ∀ t : ℝ, Summable fun n => coef f n * eχ (-Real.log n) t := fun t =>
    Summable.of_norm (hs.congr fun n => (norm_coef_mul n t).symm)
  have hcz : Continuous fun t => (starRingEnd ℂ) (riemannZeta (linePt t)) :=
    Complex.continuous_conj.comp continuous_zeta_linePt
  have hce : ∀ μ : ℝ, Continuous (eχ μ) := fun μ => _root_.GaloisForLFunctions.continuous_expChar μ
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ → ℂ, R = fun t =>
      LSeries f (linePt t) - ∑ n ∈ Finset.range M, coef f n * eχ (-Real.log n) t := ⟨_, rfl⟩
  have hRtsum : ∀ t, R t = ∑' n, coef f (n + M) * eχ (-Real.log ((n + M : ℕ) : ℝ)) t := by
    intro t
    have h1 := (hst t).sum_add_tsum_nat_add M
    simp only [hRdef]
    rw [LSeries_linePt_eq_tsum, ← h1]
    ring
  have hRb : ∀ t, ‖R t‖ ≤ tailMass f M := by
    intro t
    rw [hRtsum]
    have hsM : Summable fun n => ‖coef f (n + M)‖ :=
      (summable_nat_add_iff (f := fun n => ‖coef f n‖) M).mpr hs
    refine (norm_tsum_le_tsum_norm ?_).trans (le_of_eq ?_)
    · exact hsM.congr fun n => (norm_coef_mul (n + M) t).symm
    · unfold tailMass
      exact tsum_congr fun n => norm_coef_mul (n + M) t
  have hRc : Continuous R := by
    rw [hRdef]
    exact (continuous_LSeries_linePt hf).sub (continuous_finsetSum _ fun n _ =>
      continuous_const.mul (hce _))
  -- the integrand splits
  have hsplit : ∀ t, eχ a t * (LSeries f (linePt t) * (starRingEnd ℂ) (riemannZeta (linePt t))) =
      (∑ n ∈ Finset.range M, coef f n *
        (eχ a t * (eχ (-Real.log n) t * (starRingEnd ℂ) (riemannZeta (linePt t))))) +
      eχ a t * (R t * (starRingEnd ℂ) (riemannZeta (linePt t))) := by
    intro t
    have e : LSeries f (linePt t) =
        ∑ n ∈ Finset.range M, coef f n * eχ (-Real.log n) t + R t := by rw [hRdef]; ring
    rw [e, add_mul, mul_add, Finset.sum_mul, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun n _ => by ring
  obtain ⟨J, hJdef⟩ : ∃ J : ℕ → ℂ, J = fun n : ℕ => ∫ t in T..(2 * T),
      eχ a t * (eχ (-Real.log (n : ℝ)) t * (starRingEnd ℂ) (riemannZeta (linePt t))) := ⟨_, rfl⟩
  have hJi : ∀ n : ℕ, IntervalIntegrable (fun t => eχ a t * (eχ (-Real.log n) t *
      (starRingEnd ℂ) (riemannZeta (linePt t)))) volume T (2 * T) := fun n =>
    ((hce a).mul ((hce _).mul hcz)).intervalIntegrable _ _
  have hint : ∫ t in T..(2 * T), eχ a t *
      (LSeries f (linePt t) * (starRingEnd ℂ) (riemannZeta (linePt t))) =
      (∑ n ∈ Finset.range M, coef f n * J n) +
        ∫ t in T..(2 * T), eχ a t * (R t * (starRingEnd ℂ) (riemannZeta (linePt t))) := by
    have hI1 : IntervalIntegrable (fun t => ∑ n ∈ Finset.range M, coef f n *
        (eχ a t * (eχ (-Real.log n) t * (starRingEnd ℂ) (riemannZeta (linePt t)))))
        volume T (2 * T) :=
      (continuous_finsetSum _ fun n _ =>
        continuous_const.mul ((hce a).mul ((hce _).mul hcz))).intervalIntegrable _ _
    have hI2 : IntervalIntegrable
        (fun t => eχ a t * (R t * (starRingEnd ℂ) (riemannZeta (linePt t))))
        volume T (2 * T) := ((hce a).mul (hRc.mul hcz)).intervalIntegrable _ _
    rw [intervalIntegral.integral_congr fun t _ => hsplit t, intervalIntegral.integral_add hI1 hI2,
      intervalIntegral.integral_finsetSum fun n _ => (hJi n).const_mul _]
    congr 1
    rw [hJdef]
    exact Finset.sum_congr rfl fun n _ => intervalIntegral.integral_const_mul _ _
  -- the value splits
  have hvs : Summable fun n => coef f n * (diagWeight h k n : ℂ) := by
    refine Summable.of_norm ((hs.mul_right (Real.sqrt h)).of_nonneg_of_le (fun n => norm_nonneg _)
      fun n => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (abs_diagWeight_le hk n) (norm_nonneg _)
  have hval : twistValue f h k = (∑ n ∈ Finset.range M, coef f n * (diagWeight h k n : ℂ)) +
      ∑' n, coef f (n + M) * (diagWeight h k (n + M) : ℂ) := by
    unfold twistValue
    exact (hvs.sum_add_tsum_nat_add M).symm
  -- the three pieces
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNT : (N : ℝ) ^ 8 ≤ T := by rw [hNdef]; exact cut_pow_le hT0.le
  have hterm : ∀ n ∈ Finset.range M,
      ‖coef f n * (T⁻¹ * J n - (diagWeight h k n : ℂ))‖ ≤ ‖coef f n‖ * (K₀ / N) := by
    intro n hn
    rw [norm_mul]
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · simp
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have hnN : n ≤ N := by have := Finset.mem_range.mp hn; omega
    have h1 := norm_integral_twist_term_sub_le hh hk hn0 hT
    rw [← hadef] at h1
    have hJn : J n = ∫ t in T..(2 * T),
        eχ a t * (eχ (-Real.log n) t * (starRingEnd ℂ) (riemannZeta (linePt t))) := by rw [hJdef]
    rw [← hJn] at h1
    have hdiag : (if h ∣ k * n then ((Real.sqrt h / Real.sqrt ((k * n : ℕ) : ℝ) * T : ℝ) : ℂ)
        else 0) = (diagWeight h k n : ℂ) * T := by
      unfold diagWeight
      split_ifs
      · rw [Complex.ofReal_mul]
      · simp
    rw [hdiag] at h1
    have hTc : (T : ℂ) ≠ 0 := by exact_mod_cast hT0.ne'
    have e : ((T⁻¹ : ℝ) : ℂ) * J n - (diagWeight h k n : ℂ) =
        ((T⁻¹ : ℝ) : ℂ) * (J n - (diagWeight h k n : ℂ) * T) := by
      rw [mul_sub, Complex.ofReal_inv, mul_comm (diagWeight h k n : ℂ) (T : ℂ), ← mul_assoc,
        inv_mul_cancel₀ hTc, one_mul]
    rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hT0)]
    calc T⁻¹ * ‖J n - (diagWeight h k n : ℂ) * T‖ ≤ T⁻¹ * (Real.sqrt ((h : ℝ) * (k * n : ℕ)) *
          (27 * Real.sqrt T * (k * n : ℕ) + 8 * ((k * n : ℕ) : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hT0.le)
      _ ≤ K₀ / N := by rw [hK₀]; exact twist_term_error_le hk hn0 hnN hT hNT
  have hb1 : ‖∑ n ∈ Finset.range M, coef f n * (T⁻¹ * J n - (diagWeight h k n : ℂ))‖ ≤
      (∑' n, ‖coef f n‖) * K₀ / N := by
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
    rw [← Finset.sum_mul, mul_div_assoc]
    have hK0 : 0 ≤ K₀ := by rw [hK₀]; positivity
    exact mul_le_mul_of_nonneg_right (hs.sum_le_tsum _ fun n _ => norm_nonneg _)
      (div_nonneg hK0 (Nat.cast_nonneg _))
  have hb2 : ‖T⁻¹ * ∫ t in T..(2 * T), eχ a t * (R t * (starRingEnd ℂ) (riemannZeta (linePt t)))‖ ≤
      C * 16 * logTailMass f M := by
    have hle : ‖∫ t in T..(2 * T), eχ a t * (R t * (starRingEnd ℂ) (riemannZeta (linePt t)))‖ ≤
        ∫ t in T..(2 * T), tailMass f M * ‖riemannZeta (linePt t)‖ := by
      refine intervalIntegral.norm_integral_le_of_norm_le (by linarith) ?_
        ((continuous_const.mul continuous_zeta_linePt.norm).intervalIntegrable _ _)
      refine Filter.Eventually.of_forall fun t _ => ?_
      rw [norm_mul, norm_mul, _root_.GaloisForLFunctions.norm_expChar, one_mul, Complex.norm_conj]
      exact mul_le_mul_of_nonneg_right (hRb t) (norm_nonneg _)
    rw [intervalIntegral.integral_const_mul] at hle
    have htail0 : 0 ≤ tailMass f M := tsum_nonneg fun n => norm_nonneg _
    have hM2 : 2 ≤ M := by omega
    have htl := tailMass_le_logTailMass hf hlog hM2
    have hlM := log_cut_ge (T := T) (by linarith)
    rw [← hNdef] at hlM
    have hC0 : 0 ≤ C := by
      have h1 := hζ hT
      have h0 : 0 ≤ ∫ t in T..(2 * T), ‖riemannZeta (linePt t)‖ :=
        intervalIntegral.integral_nonneg (by linarith) fun t _ => norm_nonneg _
      by_contra hneg
      push Not at hneg
      have : C * T * (3 + Real.log T) < 0 := by
        have := mul_neg_of_neg_of_pos hneg hT0
        exact mul_neg_of_neg_of_pos this (by linarith)
      linarith
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hT0)]
    calc T⁻¹ * ‖∫ t in T..(2 * T), eχ a t * (R t * (starRingEnd ℂ) (riemannZeta (linePt t)))‖
        ≤ T⁻¹ * (tailMass f M * (C * T * (3 + Real.log T))) := by
          refine mul_le_mul_of_nonneg_left (hle.trans ?_) (inv_nonneg.mpr hT0.le)
          exact mul_le_mul_of_nonneg_left (hζ hT) htail0
      _ = C * (tailMass f M * (3 + Real.log T)) := by field_simp
      _ ≤ C * (16 * (tailMass f M * Real.log M)) := by
          refine mul_le_mul_of_nonneg_left ?_ hC0
          have : 3 + Real.log T ≤ 16 * Real.log M := by
            have : Real.log ((N + 1 : ℕ) : ℝ) = Real.log M := by rw [hMdef]
            linarith
          nlinarith
      _ ≤ C * 16 * logTailMass f M := by nlinarith
  have hb3 : ‖∑' n, coef f (n + M) * (diagWeight h k (n + M) : ℂ)‖ ≤
      Real.sqrt h * tailMass f M := by
    have hsM : Summable fun n => ‖coef f (n + M)‖ :=
      (summable_nat_add_iff (f := fun n => ‖coef f n‖) M).mpr hs
    have hbd : ∀ n, ‖coef f (n + M) * (diagWeight h k (n + M) : ℂ)‖ ≤
        Real.sqrt h * ‖coef f (n + M)‖ := fun n => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm]
      exact mul_le_mul_of_nonneg_right (abs_diagWeight_le hk _) (norm_nonneg _)
    refine (norm_tsum_le_tsum_norm ((hsM.mul_left _).of_nonneg_of_le (fun _ => norm_nonneg _)
      hbd)).trans ?_
    unfold tailMass
    rw [← tsum_mul_left]
    exact Summable.tsum_le_tsum hbd ((hsM.mul_left _).of_nonneg_of_le (fun _ => norm_nonneg _) hbd)
      (hsM.mul_left _)
  -- assemble
  have hdecomp : T⁻¹ * (∫ t in T..(2 * T), eχ a t *
        (LSeries f (linePt t) * (starRingEnd ℂ) (riemannZeta (linePt t)))) - twistValue f h k =
      (∑ n ∈ Finset.range M, coef f n * (T⁻¹ * J n - (diagWeight h k n : ℂ))) +
        T⁻¹ * (∫ t in T..(2 * T), eχ a t * (R t * (starRingEnd ℂ) (riemannZeta (linePt t)))) -
        ∑' n, coef f (n + M) * (diagWeight h k (n + M) : ℂ) := by
    have hsum : ∑ n ∈ Finset.range M, coef f n * (T⁻¹ * J n - (diagWeight h k n : ℂ)) =
        T⁻¹ * (∑ n ∈ Finset.range M, coef f n * J n) -
          ∑ n ∈ Finset.range M, coef f n * (diagWeight h k n : ℂ) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun n _ => by ring
    rw [hint, hval, hsum]
    ring
  rw [hdecomp]
  calc _ ≤ ‖(∑ n ∈ Finset.range M, coef f n * (T⁻¹ * J n - (diagWeight h k n : ℂ))) +
          T⁻¹ * (∫ t in T..(2 * T), eχ a t * (R t * (starRingEnd ℂ) (riemannZeta (linePt t))))‖ +
        ‖∑' n, coef f (n + M) * (diagWeight h k (n + M) : ℂ)‖ := norm_sub_le _ _
    _ ≤ ((∑' n, ‖coef f n‖) * K₀ / N + C * 16 * logTailMass f M) +
        Real.sqrt h * tailMass f M := add_le_add ((norm_add_le _ _).trans (add_le_add hb1 hb2)) hb3
    _ = _ := by ring

/-- **The twisted mean of `F ζ̄`.** For `h, k ≥ 1`,
`(1/T) ∫_T^{2T} (h/k)^{it} F(½+it) conj ζ(½+it) dt → Σ_n f(n) n^{−½} [h ∣ kn] √h/√(kn)`. -/
theorem tendsto_twistMean (hf : LSeriesSummable f (1 / 2))
    (hlog : LSeriesSummable (LSeries.logMul f) (1 / 2)) {h k : ℕ} (hh : 1 ≤ h) (hk : 1 ≤ k) :
    Tendsto (fun T : ℝ => T⁻¹ * ∫ t in T..(2 * T), eχ (Real.log h - Real.log k) t *
      (LSeries f (linePt t) * (starRingEnd ℂ) (riemannZeta (linePt t)))) atTop
      (𝓝 (twistValue f h k)) := by
  obtain ⟨C, hC, hζ⟩ := exists_integral_norm_zeta_line_le
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hcut1 : Tendsto (fun T => cut T + 1) atTop atTop :=
    tendsto_atTop_mono (fun T => Nat.le_succ (cut T)) tendsto_cut
  have hB : Tendsto (fun T => (∑' n, ‖coef f n‖) *
      (Real.sqrt ((h : ℝ) * k) * (27 * k + 8 * (k : ℝ) ^ 2)) / cut T +
      Real.sqrt h * tailMass f (cut T + 1) + C * 16 * logTailMass f (cut T + 1)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun T => (∑' n, ‖coef f n‖) *
        (Real.sqrt ((h : ℝ) * k) * (27 * k + 8 * (k : ℝ) ^ 2)) / (cut T : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp tendsto_cut)
    have h2 := (tendsto_tailMass (f := f)).comp hcut1
    have h3 := (tendsto_logTailMass (f := f)).comp hcut1
    simpa using (h1.add (h2.const_mul (Real.sqrt h))).add (h3.const_mul (C * 16))
  refine squeeze_zero' (Eventually.of_forall fun T => norm_nonneg _) ?_ hB
  filter_upwards [eventually_ge_atTop (4 : ℝ), Real.tendsto_log_atTop.eventually_ge_atTop 3,
    tendsto_cut.eventually_ge_atTop 1] with T h1 h2 h3
  exact norm_twistMean_sub_le hf hlog hh hk hζ h1 h2 h3

end RHTower.ZetaLineTwist
