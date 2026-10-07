import GaloisForLFunctions.RHTower.CriticalPolynomialZetaSignRigidity
import GaloisForLFunctions.RHTower.WeilZetaSquareMoments

/-!
# Twisted first moments of `ζ` on the critical line, uniformly in the twist

For positive integers `p, q` and `T ≥ 8`,

`‖∫_8^T ζ(1/2+iy) (p/q)^{iy} dy‖ ≤ C · T · √(1 + log(pq))`

with an absolute constant `C` (`exists_norm_integral_zeta_twist_le`).

* For `T ≥ (pq)⁴` the segment is moved to `Re s = 3/2`. On the right edge the term `m` of
  `ζ(3/2+iy)` contributes `T` when `mq = p` and at most `4p² m^{-3/2}` otherwise, because
  `|log p − log r| ≥ 1/(2p)` for every positive integer `r ≠ p` (`inv_two_mul_le_abs_log_sub`).
  The horizontal edges are `O(e^{|κ|} T^{1/2})` by the convexity bound.
* For `8 ≤ T < (pq)⁴` the trivial bound `∫_8^T |ζ| ≤ C T √(1 + log T)` is used. It follows from the
  mean square `∫_8^T |ζ|² ≤ C T (1 + log T)` (`exists_integral_zsq_le`), obtained from the window
  mean square by a dyadic induction, and the pointwise inequality `2λ|ζ| ≤ λ² + |ζ|²`.
-/

open Complex MeasureTheory Filter Topology Set intervalIntegral
open scoped Interval

noncomputable section

namespace RHTower.ZetaUniformMoment

open RHTower RHTower.WeilZetaSquare

/-! ## Mean square and first absolute moment on `[8, T]` -/

theorem intervalIntegrable_zsq (a b : ℝ) : IntervalIntegrable zsq volume a b :=
  continuous_zsq.intervalIntegrable a b

/-- **Mean square on `[8, T]`**: `∫_8^T |ζ(1/2+it)|² dt ≤ C T (1 + log T)`. -/
theorem exists_integral_zsq_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 8 ≤ T →
    ∫ t in (8 : ℝ)..T, zsq t ≤ C * T * (1 + Real.log T) := by
  obtain ⟨C, hC, hwin⟩ := exists_intervalIntegral_zsq_le
  set M₀ := ∫ t in (8 : ℝ)..80, zsq t with hM₀def
  have hM₀ : 0 ≤ M₀ := intervalIntegral.integral_nonneg (by norm_num) fun t _ => zsq_nonneg t
  set C₁ := max (M₀ / 8) (C / 2) with hC₁def
  have hC₁0 : 0 ≤ C₁ := le_max_of_le_right (by positivity)
  have hC₁a : M₀ / 8 ≤ C₁ := le_max_left _ _
  have hC₁b : C / 2 ≤ C₁ := le_max_right _ _
  have key : ∀ k : ℕ, ∀ T : ℝ, 8 ≤ T → T ≤ 80 * 5 ^ k →
      ∫ t in (8 : ℝ)..T, zsq t ≤ C₁ * T * (1 + Real.log T) := by
    intro k
    induction k with
    | zero =>
      intro T hT hT80
      have hT80' : T ≤ 80 := by simpa using hT80
      have h1 : ∫ t in (8 : ℝ)..T, zsq t ≤ M₀ :=
        intervalIntegral.integral_mono_interval (le_refl _) hT hT80'
          (Eventually.of_forall fun t => zsq_nonneg t) (intervalIntegrable_zsq _ _)
      have hlog : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
      have h2 : M₀ ≤ C₁ * T * (1 + Real.log T) := by
        have : M₀ ≤ C₁ * 8 := by linarith
        have h3 : C₁ * 8 ≤ C₁ * T := mul_le_mul_of_nonneg_left hT hC₁0
        have h4 : C₁ * T ≤ C₁ * T * (1 + Real.log T) := by
          have : 0 ≤ C₁ * T := mul_nonneg hC₁0 (by linarith)
          nlinarith
        linarith
      linarith
    | succ k ih =>
      intro T hT hTk
      by_cases hTle : T ≤ 80 * 5 ^ k
      · exact ih T hT hTle
      · push Not at hTle
        have h5k : (1 : ℝ) ≤ 5 ^ k := one_le_pow₀ (by norm_num)
        have hT80 : 80 < T := by nlinarith
        have hsplit : ∫ t in (8 : ℝ)..T, zsq t =
            (∫ t in (8 : ℝ)..T / 5, zsq t) + ∫ t in (T / 5)..T, zsq t :=
          (intervalIntegral.integral_add_adjacent_intervals (intervalIntegrable_zsq _ _)
            (intervalIntegrable_zsq _ _)).symm
        have hA := ih (T / 5) (by linarith) (by rw [pow_succ] at hTk; linarith)
        have hB : ∫ t in (T / 5)..T, zsq t ≤ C * (2 * T / 5) * Real.log (2 * T / 5) := by
          have h := hwin (L := 2 * T / 5) (by linarith)
          rwa [show 2 * T / 5 / 2 = T / 5 by ring, show 5 * (2 * T / 5) / 2 = T by ring] at h
        have hlog1 : Real.log (T / 5) ≤ Real.log T := Real.log_le_log (by positivity) (by linarith)
        have hlog2 : Real.log (2 * T / 5) ≤ Real.log T := Real.log_le_log (by positivity) (by linarith)
        have hlog3 : 0 ≤ Real.log (2 * T / 5) := Real.log_nonneg (by linarith)
        have hlogT : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
        have hT0 : 0 ≤ T := by linarith
        have e1 : C₁ * (T / 5) * (1 + Real.log (T / 5)) ≤ C₁ * (T / 5) * (1 + Real.log T) := by
          have : 0 ≤ C₁ * (T / 5) := by positivity
          nlinarith
        have e2 : C * (2 * T / 5) * Real.log (2 * T / 5) ≤ (2 * C₁) * (2 * T / 5) * (1 + Real.log T) := by
          have h2C : C ≤ 2 * C₁ := by linarith
          have : 0 ≤ 2 * T / 5 := by positivity
          calc C * (2 * T / 5) * Real.log (2 * T / 5) ≤ C * (2 * T / 5) * (1 + Real.log T) := by
                have : 0 ≤ C * (2 * T / 5) := by positivity
                nlinarith
            _ ≤ (2 * C₁) * (2 * T / 5) * (1 + Real.log T) := by
                have : 0 ≤ (2 * T / 5) * (1 + Real.log T) := by positivity
                nlinarith
        rw [hsplit]
        calc (∫ t in (8 : ℝ)..T / 5, zsq t) + ∫ t in (T / 5)..T, zsq t
            ≤ C₁ * (T / 5) * (1 + Real.log (T / 5)) + C * (2 * T / 5) * Real.log (2 * T / 5) :=
              add_le_add hA hB
          _ ≤ C₁ * (T / 5) * (1 + Real.log T) + (2 * C₁) * (2 * T / 5) * (1 + Real.log T) :=
              add_le_add e1 e2
          _ = C₁ * T * (1 + Real.log T) := by ring
  refine ⟨C₁, hC₁0, fun T hT => ?_⟩
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (T / 80) (by norm_num : (1 : ℝ) < 5)
  exact key k T hT (by linarith [hk.le])

theorem zsq_eq_norm_sq (t : ℝ) : zsq t = ‖riemannZeta ((1 / 2 : ℂ) + t * I)‖ ^ 2 := by
  rw [zsq, Complex.normSq_eq_norm_sq]
  simp [linePt]

theorem continuous_norm_zeta_line :
    Continuous fun t : ℝ => ‖riemannZeta ((1 / 2 : ℂ) + t * I)‖ :=
  continuous_riemannZeta_criticalLine.norm

/-- **First absolute moment on `[8, T]`**: `∫_8^T |ζ(1/2+it)| dt ≤ C T √(1 + log T)`. -/
theorem exists_integral_norm_zeta_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 8 ≤ T →
    ∫ t in (8 : ℝ)..T, ‖riemannZeta ((1 / 2 : ℂ) + t * I)‖ ≤ C * T * Real.sqrt (1 + Real.log T) := by
  obtain ⟨C₁, hC₁, hms⟩ := exists_integral_zsq_le
  refine ⟨(1 + C₁) / 2, by positivity, fun T hT => ?_⟩
  have hlog : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  set lam0 := Real.sqrt (1 + Real.log T) with hlam
  have hlampos : 0 < lam0 := Real.sqrt_pos.mpr (by linarith)
  have hlamsq : lam0 ^ 2 = 1 + Real.log T := Real.sq_sqrt (by linarith)
  have hpt : ∀ t ∈ Set.Icc (8 : ℝ) T, ‖riemannZeta ((1 / 2 : ℂ) + t * I)‖ ≤
      lam0 / 2 + zsq t / (2 * lam0) := by
    intro t _
    rw [zsq_eq_norm_sq]
    set x := ‖riemannZeta ((1 / 2 : ℂ) + t * I)‖
    rw [div_add_div _ _ (by norm_num : (2 : ℝ) ≠ 0) (by positivity), le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (x - lam0)]
  have hmono : (∫ t in (8 : ℝ)..T, ‖riemannZeta ((1 / 2 : ℂ) + t * I)‖) ≤
      ∫ t in (8 : ℝ)..T, (lam0 / 2 + zsq t / (2 * lam0)) :=
    intervalIntegral.integral_mono_on (μ := volume) hT (continuous_norm_zeta_line.intervalIntegrable _ _)
      ((continuous_const.add (continuous_zsq.div_const _)).intervalIntegrable _ _) hpt
  have hsplit : ∫ t in (8 : ℝ)..T, (lam0 / 2 + zsq t / (2 * lam0)) =
      lam0 / 2 * (T - 8) + (∫ t in (8 : ℝ)..T, zsq t) / (2 * lam0) := by
    rw [intervalIntegral.integral_add intervalIntegrable_const
      ((continuous_zsq.div_const _).intervalIntegrable _ _), intervalIntegral.integral_const,
      intervalIntegral.integral_div, smul_eq_mul]
    ring
  rw [hsplit] at hmono
  have hms' := hms T hT
  have h2 : (∫ t in (8 : ℝ)..T, zsq t) / (2 * lam0) ≤ C₁ * T * lam0 / 2 := by
    rw [div_le_iff₀ (by positivity)]
    calc (∫ t in (8 : ℝ)..T, zsq t) ≤ C₁ * T * (1 + Real.log T) := hms'
      _ = C₁ * T * lam0 / 2 * (2 * lam0) := by rw [← hlamsq]; ring
  have h3 : lam0 / 2 * (T - 8) ≤ lam0 / 2 * T := by
    have : 0 ≤ lam0 / 2 := by positivity
    nlinarith
  calc ∫ t in (8 : ℝ)..T, ‖riemannZeta ((1 / 2 : ℂ) + t * I)‖
      ≤ lam0 / 2 * (T - 8) + (∫ t in (8 : ℝ)..T, zsq t) / (2 * lam0) := hmono
    _ ≤ lam0 / 2 * T + C₁ * T * lam0 / 2 := add_le_add h3 h2
    _ = (1 + C₁) / 2 * T * lam0 := by ring

/-! ## The contour bound -/

/-- `∫_8^T e^{iδy} dy` has norm at most `2/|δ|` for `δ ≠ 0`. -/
theorem norm_integral_cexp_le {δ : ℝ} (hδ : δ ≠ 0) (T : ℝ) :
    ‖∫ y in (8 : ℝ)..T, cexp ((δ : ℂ) * y * I)‖ ≤ 2 / |δ| := by
  rw [integral_cexp_ofReal_mul_I, if_neg hδ, norm_div, norm_mul, norm_I, mul_one,
    Complex.norm_real, Real.norm_eq_abs]
  gcongr
  calc ‖cexp (δ * T * I) - cexp (δ * 8 * I)‖ ≤ ‖cexp (δ * T * I)‖ + ‖cexp (δ * 8 * I)‖ :=
        norm_sub_le _ _
    _ = 2 := by
      rw [show ((δ : ℂ) * T * I) = ((δ * T : ℝ) : ℂ) * I by push_cast; ring,
        show ((δ : ℂ) * 8 * I) = ((δ * 8 : ℝ) : ℂ) * I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I, Complex.norm_exp_ofReal_mul_I]
      norm_num

/-- `∫_8^T e^{iδy} dy` has norm at most `T` for `T ≥ 8`. -/
theorem norm_integral_cexp_le_length (δ : ℝ) {T : ℝ} (hT : 8 ≤ T) :
    ‖∫ y in (8 : ℝ)..T, cexp ((δ : ℂ) * y * I)‖ ≤ T := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (8 : ℝ)) (b := T)
    (f := fun y : ℝ => cexp ((δ : ℂ) * y * I)) (C := 1) (fun y _ => by
      rw [show ((δ : ℂ) * y * I) = ((δ * y : ℝ) : ℂ) * I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I])
  rw [abs_of_nonneg (by linarith)] at h
  linarith

/-- **Logarithmic separation**: `|log p − log r| ≥ 1/(2p)` for positive integers `r ≠ p`. -/
theorem inv_two_mul_le_abs_log_sub {p r : ℕ} (hp : 1 ≤ p) (hr : 1 ≤ r) (hne : r ≠ p) :
    1 / (2 * (p : ℝ)) ≤ |Real.log p - Real.log r| := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hpos : 0 < 1 / (2 * (p : ℝ)) := by positivity
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · have hlt' : (r : ℝ) + 1 ≤ p := by exact_mod_cast hlt
    have hlog := Real.one_sub_inv_le_log_of_pos (div_pos hp0 hr0)
    rw [Real.log_div hp0.ne' hr0.ne', inv_div] at hlog
    have h1 : 1 / (2 * (p : ℝ)) ≤ 1 - r / p := by
      have e : 1 - (r : ℝ) / p = (p - r) / p := by field_simp
      rw [e, div_le_div_iff₀ (by positivity) hp0]
      nlinarith
    rw [abs_of_nonneg (by linarith)]
    linarith
  · have hgt' : (p : ℝ) + 1 ≤ r := by exact_mod_cast hgt
    have hlog := Real.one_sub_inv_le_log_of_pos (div_pos hr0 hp0)
    rw [Real.log_div hr0.ne' hp0.ne', inv_div] at hlog
    have h1 : 1 / (2 * (p : ℝ)) ≤ 1 - p / r := by
      have e : 1 - (p : ℝ) / r = (r - p) / r := by field_simp
      rw [e, div_le_div_iff₀ (by positivity) hr0]
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ r - p - 1) (by linarith : (0 : ℝ) ≤ 2 * p - 1)]
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith

/-- The horizontal edges, with the twist dependence explicit. -/
theorem exists_norm_horizontal_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ κ T : ℝ, 8 ≤ T →
    ‖∫ x in (1 / 2 : ℝ)..(3 / 2 : ℝ), expTwistedZeta κ (x + T * I)‖ ≤
      C * Real.exp |κ| * T ^ (1 / 2 : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_riemannZeta_le_convexity (η := 1 / 2) (by norm_num)
    (by norm_num)
  refine ⟨C, hC.le, fun κ T hT => ?_⟩
  have hT1 : (1 : ℝ) ≤ T := by linarith
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (1 / 2 : ℝ)) (b := 3 / 2)
    (f := fun x : ℝ => expTwistedZeta κ (x + T * I)) (C := C * Real.exp |κ| * T ^ (1 / 2 : ℝ)) ?_
  · calc _ ≤ C * Real.exp |κ| * T ^ (1 / 2 : ℝ) * |(3 / 2 : ℝ) - 1 / 2| := h
      _ = C * Real.exp |κ| * T ^ (1 / 2 : ℝ) := by norm_num
  · intro x hx
    rw [Set.uIoc_of_le (by norm_num)] at hx
    have hx1 : 1 / 2 < x := hx.1
    have hx2 : x ≤ 3 / 2 := hx.2
    rw [expTwistedZeta, norm_mul]
    have hz := hbound x T (by linarith) (by linarith) hT
    have hexp : ‖cexp ((κ : ℂ) * ((x : ℂ) + T * I - 1 / 2))‖ ≤ Real.exp |κ| := by
      rw [Complex.norm_exp]
      apply Real.exp_le_exp.mpr
      have hre : ((κ : ℂ) * ((x : ℂ) + T * I - 1 / 2)).re = κ * (x - 1 / 2) := by simp
      rw [hre]
      have h0 : 0 ≤ x - 1 / 2 := by linarith
      have h1 : x - 1 / 2 ≤ 1 := by linarith
      calc κ * (x - 1 / 2) ≤ |κ * (x - 1 / 2)| := le_abs_self _
        _ = |κ| * (x - 1 / 2) := by rw [abs_mul, abs_of_nonneg h0]
        _ ≤ |κ| * 1 := by gcongr
        _ = |κ| := mul_one _
    have hpow : T ^ ((1 + 1 / 2 - x) / 2) ≤ T ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)
    calc ‖riemannZeta ((x : ℂ) + T * I)‖ * ‖cexp ((κ : ℂ) * ((x : ℂ) + T * I - 1 / 2))‖
        ≤ (C * T ^ ((1 + 1 / 2 - x) / 2)) * Real.exp |κ| := by gcongr
      _ ≤ (C * T ^ (1 / 2 : ℝ)) * Real.exp |κ| := by gcongr
      _ = C * Real.exp |κ| * T ^ (1 / 2 : ℝ) := by ring

/-- The rectangle identity: the critical segment equals the right edge plus the horizontal edges. -/
theorem integral_line_eq (κ : ℝ) {T : ℝ} (hT : 8 ≤ T) :
    ∫ y in (8 : ℝ)..T, riemannZeta ((1 / 2 : ℂ) + y * I) * cexp ((κ : ℂ) * y * I) =
      (∫ y in (8 : ℝ)..T, riemannZeta ((3 / 2 : ℂ) + y * I) *
        cexp ((κ : ℂ) * (((3 / 2 : ℂ) + y * I) - 1 / 2))) +
      ((∫ x in (1 / 2 : ℝ)..(3 / 2 : ℝ), expTwistedZeta κ (x + 8 * I)) -
        (∫ x in (1 / 2 : ℝ)..(3 / 2 : ℝ), expTwistedZeta κ (x + T * I))) / I := by
  have hre1 : ((1 / 2 : ℂ) + 8 * I).re = 1 / 2 := by simp
  have hre2 : ((3 / 2 : ℂ) + T * I).re = 3 / 2 := by simp
  have him1 : ((1 / 2 : ℂ) + 8 * I).im = 8 := by simp
  have him2 : ((3 / 2 : ℂ) + T * I).im = T := by simp
  have h := integral_boundary_rect_eq_zero_of_differentiableOn (expTwistedZeta κ)
    ((1 / 2 : ℂ) + 8 * I) ((3 / 2 : ℂ) + T * I) (by
      rw [hre1, hre2, him1, him2]; exact differentiableOn_twistedZeta_rect κ hT)
  rw [hre1, hre2, him1, him2] at h
  have hL : ∫ y in (8 : ℝ)..T, expTwistedZeta κ (((1 / 2 : ℝ) : ℂ) + y * I) =
      ∫ y in (8 : ℝ)..T, riemannZeta ((1 / 2 : ℂ) + y * I) * cexp ((κ : ℂ) * y * I) := by
    congr 1; funext y; simp only [expTwistedZeta]; push_cast; ring_nf
  have hR : ∫ y in (8 : ℝ)..T, expTwistedZeta κ (((3 / 2 : ℝ) : ℂ) + y * I) =
      ∫ y in (8 : ℝ)..T, riemannZeta ((3 / 2 : ℂ) + y * I) *
        cexp ((κ : ℂ) * (((3 / 2 : ℂ) + y * I) - 1 / 2)) := by
    congr 1; funext y; simp only [expTwistedZeta]; push_cast; ring_nf
  have h8 : ∫ x in (1 / 2 : ℝ)..(3 / 2 : ℝ), expTwistedZeta κ (x + ((8 : ℝ) : ℂ) * I) =
      ∫ x in (1 / 2 : ℝ)..(3 / 2 : ℝ), expTwistedZeta κ (x + 8 * I) := by push_cast; rfl
  rw [hL, hR, h8] at h
  rw [smul_eq_mul, smul_eq_mul] at h
  generalize (∫ y in (8 : ℝ)..T, riemannZeta ((1 / 2 : ℂ) + y * I) * cexp ((κ : ℂ) * y * I)) = L at h ⊢
  generalize (∫ y in (8 : ℝ)..T, riemannZeta ((3 / 2 : ℂ) + y * I) *
    cexp ((κ : ℂ) * (((3 / 2 : ℂ) + y * I) - 1 / 2))) = R at h ⊢
  generalize (∫ x in (1 / 2 : ℝ)..(3 / 2 : ℝ), expTwistedZeta κ (x + 8 * I)) = A at h ⊢
  generalize (∫ x in (1 / 2 : ℝ)..(3 / 2 : ℝ), expTwistedZeta κ (x + T * I)) = B at h ⊢
  have h' : I * L = I * R + (A - B) := by linear_combination -h
  calc L = (I * L) / I := by rw [mul_div_cancel_left₀ _ I_ne_zero]
    _ = (I * R + (A - B)) / I := by rw [h']
    _ = R + (A - B) / I := by rw [add_div, mul_div_cancel_left₀ _ I_ne_zero]

/-- `Σ m^{-3/2}`. -/
def zeta32 : ℝ := ∑' m : ℕ, (m : ℝ) ^ (-(3 / 2 : ℝ))

theorem summable_rpow_neg_three_halves : Summable fun m : ℕ => (m : ℝ) ^ (-(3 / 2 : ℝ)) :=
  Real.summable_nat_rpow.mpr (by norm_num)

theorem zeta32_nonneg : 0 ≤ zeta32 :=
  tsum_nonneg fun m => Real.rpow_nonneg (Nat.cast_nonneg m) _

/-- One term of the right edge, for the twist `κ = log p − log q`. -/
theorem norm_integral_rightEdgeTerm_le {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) (m : ℕ) {T : ℝ}
    (hT : 8 ≤ T) :
    ‖∫ y in (8 : ℝ)..T, rightEdgeTerm (Real.log p - Real.log q) m y‖ ≤
      4 * (p : ℝ) ^ 2 * (m : ℝ) ^ (-(3 / 2 : ℝ)) + (if m * q = p then T else 0) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hT0 : 0 ≤ T := by linarith
  have hrhs0 : 0 ≤ 4 * (p : ℝ) ^ 2 * (m : ℝ) ^ (-(3 / 2 : ℝ)) :=
    mul_nonneg (by positivity) (Real.rpow_nonneg (Nat.cast_nonneg m) _)
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simp only [rightEdgeTerm_zero, intervalIntegral.integral_zero, norm_zero]
    split_ifs <;> linarith
  · set κ := Real.log p - Real.log q with hκ
    have hexpκ : Real.exp κ = p / q := by
      rw [hκ, Real.exp_sub, Real.exp_log hp0, Real.exp_log hq0]
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
    rw [integral_rightEdgeTerm hm, norm_mul, norm_mul, Complex.norm_exp_ofReal, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg m) _), hexpκ]
    have hmpow : 0 ≤ (m : ℝ) ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg m) _
    by_cases hres : m * q = p
    · rw [if_pos hres]
      have hpq : (p : ℝ) / q = m := by
        rw [div_eq_iff hq0.ne']; exact_mod_cast hres.symm
      rw [hpq]
      have hI := norm_integral_cexp_le_length (κ - Real.log m) hT
      have hmm : (m : ℝ) * (m : ℝ) ^ (-(3 / 2 : ℝ)) ≤ 1 := by
        rw [show (m : ℝ) * (m : ℝ) ^ (-(3 / 2 : ℝ)) = (m : ℝ) ^ (-(1 / 2 : ℝ)) by
          rw [show (-(1 / 2 : ℝ)) = 1 + (-(3 / 2)) by norm_num, Real.rpow_add hm0, Real.rpow_one] ]
        exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hm) (by norm_num)
      calc (m : ℝ) * (m : ℝ) ^ (-(3 / 2 : ℝ)) * ‖∫ y in (8 : ℝ)..T,
            cexp (((κ - Real.log m : ℝ) : ℂ) * y * I)‖ ≤ 1 * T := by
            gcongr
        _ ≤ 4 * (p : ℝ) ^ 2 * (m : ℝ) ^ (-(3 / 2 : ℝ)) + T := by linarith
    · rw [if_neg hres, add_zero]
      have hmq : 1 ≤ m * q := Nat.one_le_iff_ne_zero.mpr (by positivity)
      have hsep := inv_two_mul_le_abs_log_sub hp hmq hres
      have hδ : κ - Real.log m = Real.log p - Real.log (m * q : ℕ) := by
        rw [hκ]; push_cast
        rw [Real.log_mul hm0.ne' hq0.ne']; ring
      have hδne : κ - Real.log m ≠ 0 := by
        intro h0
        rw [hδ] at h0
        rw [h0, abs_zero] at hsep
        have : 0 < 1 / (2 * (p : ℝ)) := by positivity
        linarith
      have hI := norm_integral_cexp_le hδne T
      have hI' : 2 / |κ - Real.log m| ≤ 4 * p := by
        rw [hδ, div_le_iff₀ (by
          have : 0 < 1 / (2 * (p : ℝ)) := by positivity
          linarith)]
        have : 1 ≤ 2 * p * |Real.log p - Real.log (m * q : ℕ)| := by
          rw [div_le_iff₀ (by positivity)] at hsep; linarith
        nlinarith
      have hpq : (p : ℝ) / q ≤ p := div_le_self hp0.le (by exact_mod_cast hq)
      calc (p : ℝ) / q * (m : ℝ) ^ (-(3 / 2 : ℝ)) * ‖∫ y in (8 : ℝ)..T,
            cexp (((κ - Real.log m : ℝ) : ℂ) * y * I)‖
          ≤ p * (m : ℝ) ^ (-(3 / 2 : ℝ)) * (4 * p) := by
            gcongr
            exact hI.trans hI'
        _ = 4 * (p : ℝ) ^ 2 * (m : ℝ) ^ (-(3 / 2 : ℝ)) := by ring

/-- **The right edge**, for the twist `κ = log p − log q`: at most `T + 4p² Σ m^{-3/2}`. -/
theorem norm_rightEdge_le {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) {T : ℝ} (hT : 8 ≤ T) :
    ‖∫ y in (8 : ℝ)..T, riemannZeta ((3 / 2 : ℂ) + y * I) *
        cexp (((Real.log p - Real.log q : ℝ) : ℂ) * (((3 / 2 : ℂ) + y * I) - 1 / 2))‖ ≤
      T + 4 * (p : ℝ) ^ 2 * zeta32 := by
  set κ := Real.log p - Real.log q with hκ
  have hT0 : 0 ≤ T := by linarith
  set g : ℕ → ℝ := fun m => 4 * (p : ℝ) ^ 2 * (m : ℝ) ^ (-(3 / 2 : ℝ)) +
    (if m * q = p then T else 0) with hg
  have hsumite : Summable fun m : ℕ => (if m * q = p then T else 0) := by
    refine summable_of_ne_finset_zero (s := {p / q}) fun m hm => ?_
    rw [if_neg]
    intro h
    apply hm
    rw [Finset.mem_singleton, ← h, Nat.mul_div_cancel _ (by omega)]
  have hgs : Summable g := (summable_rpow_neg_three_halves.mul_left _).add hsumite
  have hite : ∑' m : ℕ, (if m * q = p then T else 0) ≤ T := by
    rw [tsum_eq_single (p / q)]
    · split_ifs <;> linarith
    · intro m hm
      rw [if_neg]
      intro h
      apply hm
      rw [← h, Nat.mul_div_cancel _ (by omega)]
  have hnorm : ∀ m, ‖∫ y in (8 : ℝ)..T, rightEdgeTerm κ m y‖ ≤ g m := fun m =>
    norm_integral_rightEdgeTerm_le hp hq m hT
  rw [← (hasSum_integral_rightEdgeTerm κ T).tsum_eq]
  calc ‖∑' m, ∫ y in (8 : ℝ)..T, rightEdgeTerm κ m y‖
      ≤ ∑' m, ‖∫ y in (8 : ℝ)..T, rightEdgeTerm κ m y‖ :=
        norm_tsum_le_tsum_norm (Summable.of_nonneg_of_le (fun m => norm_nonneg _) hnorm hgs)
    _ ≤ ∑' m, g m :=
        Summable.tsum_le_tsum hnorm (Summable.of_nonneg_of_le (fun m => norm_nonneg _) hnorm hgs) hgs
    _ = 4 * (p : ℝ) ^ 2 * zeta32 + ∑' m : ℕ, (if m * q = p then T else 0) := by
        rw [hg, Summable.tsum_add (summable_rpow_neg_three_halves.mul_left _) hsumite, tsum_mul_left]
        rfl
    _ ≤ T + 4 * (p : ℝ) ^ 2 * zeta32 := by linarith

theorem exp_abs_log_sub_le {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) :
    Real.exp |Real.log p - Real.log q| ≤ (p : ℝ) * q := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hlp : 0 ≤ Real.log p := Real.log_nonneg hp1
  have hlq : 0 ≤ Real.log q := Real.log_nonneg hq1
  have h : |Real.log p - Real.log q| ≤ Real.log ((p : ℝ) * q) := by
    rw [Real.log_mul (by positivity) (by positivity), abs_le]
    constructor <;> linarith
  calc Real.exp |Real.log p - Real.log q| ≤ Real.exp (Real.log ((p : ℝ) * q)) := Real.exp_le_exp.mpr h
    _ = (p : ℝ) * q := Real.exp_log (by positivity)

/-- **Uniform twisted first moment.** For positive integers `p, q` and `T ≥ 8`,
`‖∫_8^T ζ(1/2+iy) (p/q)^{iy} dy‖ ≤ C T √(1 + log(pq))`. -/
theorem exists_norm_integral_zeta_twist_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ p q : ℕ, 1 ≤ p → 1 ≤ q →
    ∀ T : ℝ, 8 ≤ T →
      ‖∫ y in (8 : ℝ)..T, riemannZeta ((1 / 2 : ℂ) + y * I) *
          cexp (((Real.log p - Real.log q : ℝ) : ℂ) * y * I)‖ ≤
        C * T * Real.sqrt (1 + Real.log ((p : ℝ) * q)) := by
  obtain ⟨Ch, hCh, hhor⟩ := exists_norm_horizontal_le
  obtain ⟨Ca, hCa, habs⟩ := exists_integral_norm_zeta_le
  refine ⟨max (1 + 4 * zeta32 + 2 * Ch) (2 * Ca), le_max_of_le_right (by positivity),
    fun p q hp hq T hT => ?_⟩
  set κ := Real.log p - Real.log q with hκ
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hpq1 : (1 : ℝ) ≤ (p : ℝ) * q := one_le_mul_of_one_le_of_one_le hp1 hq1
  have hlogpq : 0 ≤ Real.log ((p : ℝ) * q) := Real.log_nonneg hpq1
  have hsq1 : 1 ≤ Real.sqrt (1 + Real.log ((p : ℝ) * q)) := Real.one_le_sqrt.mpr (by linarith)
  have hT0 : 0 ≤ T := by linarith
  by_cases hbig : ((p : ℝ) * q) ^ 4 ≤ T
  · -- contour bound
    set s := Real.sqrt T with hs
    have hs1 : 1 ≤ s := Real.one_le_sqrt.mpr (by linarith)
    have hss : s * s = T := Real.mul_self_sqrt hT0
    have hTs : T ^ (1 / 2 : ℝ) = s := by rw [hs, Real.sqrt_eq_rpow]
    have h8s : (8 : ℝ) ^ (1 / 2 : ℝ) ≤ s := by
      rw [← hTs]; exact Real.rpow_le_rpow (by norm_num) hT (by norm_num)
    have hpq2 : ((p : ℝ) * q) ^ 2 ≤ s := by
      have h4 : (((p : ℝ) * q) ^ 2) ^ 2 ≤ s ^ 2 := by
        rw [← pow_mul, sq s, hss]; exact hbig
      exact le_of_pow_le_pow_left₀ two_ne_zero (by positivity) h4
    have hpq_s : (p : ℝ) * q ≤ s := le_trans (by nlinarith) hpq2
    have hp2 : (p : ℝ) ^ 2 ≤ T := by
      have h1 : (p : ℝ) ^ 2 ≤ ((p : ℝ) * q) ^ 2 := by
        rw [mul_pow]
        have : (1 : ℝ) ≤ (q : ℝ) ^ 2 := one_le_pow₀ hq1
        calc (p : ℝ) ^ 2 = (p : ℝ) ^ 2 * 1 := (mul_one _).symm
          _ ≤ (p : ℝ) ^ 2 * (q : ℝ) ^ 2 := mul_le_mul_of_nonneg_left this (by positivity)
      have h2 : s ≤ T := by rw [← hss]; nlinarith
      linarith
    have hexp := exp_abs_log_sub_le hp hq
    have hA := hhor κ 8 (le_refl _)
    have hB := hhor κ T hT
    have hR := norm_rightEdge_le hp hq hT
    rw [integral_line_eq κ hT]
    calc ‖(∫ y in (8 : ℝ)..T, riemannZeta ((3 / 2 : ℂ) + y * I) *
            cexp ((κ : ℂ) * (((3 / 2 : ℂ) + y * I) - 1 / 2))) +
          ((∫ x in (1 / 2 : ℝ)..(3 / 2 : ℝ), expTwistedZeta κ (x + 8 * I)) -
            (∫ x in (1 / 2 : ℝ)..(3 / 2 : ℝ), expTwistedZeta κ (x + T * I))) / I‖
        ≤ (T + 4 * (p : ℝ) ^ 2 * zeta32) +
            (Ch * Real.exp |κ| * (8 : ℝ) ^ (1 / 2 : ℝ) + Ch * Real.exp |κ| * T ^ (1 / 2 : ℝ)) := by
          refine (norm_add_le _ _).trans (add_le_add hR ?_)
          rw [norm_div, norm_I, div_one]
          exact (norm_sub_le _ _).trans (add_le_add hA hB)
      _ ≤ (T + 4 * T * zeta32) + (Ch * T + Ch * T) := by
          have hz := zeta32_nonneg
          have hE0 : 0 ≤ Ch * Real.exp |κ| := by positivity
          have e1 : Ch * Real.exp |κ| * (8 : ℝ) ^ (1 / 2 : ℝ) ≤ Ch * T := by
            calc Ch * Real.exp |κ| * (8 : ℝ) ^ (1 / 2 : ℝ) ≤ Ch * ((p : ℝ) * q) * s := by
                  gcongr
              _ ≤ Ch * s * s := by gcongr
              _ = Ch * T := by rw [mul_assoc, hss]
          have e2 : Ch * Real.exp |κ| * T ^ (1 / 2 : ℝ) ≤ Ch * T := by
            rw [hTs]
            calc Ch * Real.exp |κ| * s ≤ Ch * ((p : ℝ) * q) * s := by gcongr
              _ ≤ Ch * s * s := by gcongr
              _ = Ch * T := by rw [mul_assoc, hss]
          have e3 : 4 * (p : ℝ) ^ 2 * zeta32 ≤ 4 * T * zeta32 := by gcongr
          linarith
      _ = (1 + 4 * zeta32 + 2 * Ch) * T := by ring
      _ ≤ max (1 + 4 * zeta32 + 2 * Ch) (2 * Ca) * T * Real.sqrt (1 + Real.log ((p : ℝ) * q)) := by
          have hmax : 1 + 4 * zeta32 + 2 * Ch ≤ max (1 + 4 * zeta32 + 2 * Ch) (2 * Ca) := le_max_left _ _
          have h0 : 0 ≤ max (1 + 4 * zeta32 + 2 * Ch) (2 * Ca) * T := by positivity
          calc (1 + 4 * zeta32 + 2 * Ch) * T ≤ max (1 + 4 * zeta32 + 2 * Ch) (2 * Ca) * T := by
                gcongr
            _ ≤ _ := by nlinarith
  · -- trivial bound
    push Not at hbig
    have hTpos : 0 < T := by linarith
    have hlogT : Real.log T ≤ 4 * Real.log ((p : ℝ) * q) := by
      have h := Real.log_le_log hTpos hbig.le
      rw [Real.log_pow] at h
      push_cast at h
      linarith
    have hsqrt : Real.sqrt (1 + Real.log T) ≤ 2 * Real.sqrt (1 + Real.log ((p : ℝ) * q)) := by
      rw [show (2 : ℝ) * Real.sqrt (1 + Real.log ((p : ℝ) * q)) =
        Real.sqrt (4 * (1 + Real.log ((p : ℝ) * q))) by
          rw [Real.sqrt_mul (by norm_num), show Real.sqrt 4 = 2 by
            rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)] ] ]
      exact Real.sqrt_le_sqrt (by linarith)
    have h1 : ‖∫ y in (8 : ℝ)..T, riemannZeta ((1 / 2 : ℂ) + y * I) * cexp ((κ : ℂ) * y * I)‖ ≤
        ∫ y in (8 : ℝ)..T, ‖riemannZeta ((1 / 2 : ℂ) + y * I)‖ := by
      refine (intervalIntegral.norm_integral_le_integral_norm hT).trans (le_of_eq ?_)
      congr 1; funext y
      rw [norm_mul, show ((κ : ℂ) * y * I) = ((κ * y : ℝ) : ℂ) * I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I, mul_one]
    calc ‖∫ y in (8 : ℝ)..T, riemannZeta ((1 / 2 : ℂ) + y * I) * cexp ((κ : ℂ) * y * I)‖
        ≤ Ca * T * Real.sqrt (1 + Real.log T) := h1.trans (habs T hT)
      _ ≤ Ca * T * (2 * Real.sqrt (1 + Real.log ((p : ℝ) * q))) := by gcongr
      _ = (2 * Ca) * T * Real.sqrt (1 + Real.log ((p : ℝ) * q)) := by ring
      _ ≤ max (1 + 4 * zeta32 + 2 * Ch) (2 * Ca) * T * Real.sqrt (1 + Real.log ((p : ℝ) * q)) := by
          gcongr; exact le_max_right _ _

end RHTower.ZetaUniformMoment
