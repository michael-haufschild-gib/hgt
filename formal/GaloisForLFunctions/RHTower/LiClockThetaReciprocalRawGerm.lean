import GaloisForLFunctions.RHTower.LiEvenCrossActualClockCumulantBoundary

/-!
# The reciprocal-coordinate raw germ of the actual generator

For fixed `z > 0` put `Q_z(u) = Φ(z/(1 - zu))/Φ(z)`.  Expanding `(1 - zu)^{-2j}` by the
negative binomial series and exchanging the nonnegative double series gives, on `|u| < 1/z`,
`Q_z(u) = Σ_n a_n(z) u^n` with
`a_n(z) = z^n/Φ(z) · Σ_j c_j z^{2j} C(2j+n-1, n)`, `c_j = ν_j/(2j)!`.

* every `a_n > 0`, and `a_n ≥ (ν₁ z²/(2Φ(z))) (n+1) z^n`;
* the radius of the coefficient series is exactly `1/z`;
* the ratios `a_{n+1}/a_n` drop strictly infinitely often (the coefficients are not eventually
  log-convex);
* `log Q_z(u) = H(p - u) - H(p)` with `p = 1/z`, so its Taylor coefficients are
  `b_n = (-1)^n H^{(n)}(p)/n!`, and `Q' = Q (log Q)'` gives `(n+1) a_{n+1} = Σ_k (k+1) b_{k+1} a_{n-k}`.
-/

open Set Filter Topology MeasureTheory GaloisForLFunctions.HTGeometry
open scoped ContDiff

noncomputable section

namespace RHTower

local notation "Φ" => liClockThetaGeneratorReal

/-! ## The negative binomial series -/

theorem hasSum_negBinomial (m : ℕ) {w : ℂ} (hw : ‖w‖ < 1) :
    HasSum (fun n : ℕ => (((m + n - 1).choose n : ℕ) : ℂ) * w ^ n) ((1 - w) ^ m)⁻¹ := by
  rcases m with _ | k
  · have h : HasSum (fun n : ℕ => (((0 + n - 1).choose n : ℕ) : ℂ) * w ^ n)
        ((((0 + 0 - 1).choose 0 : ℕ) : ℂ) * w ^ 0) :=
      hasSum_single 0 fun n hn => by
        rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul]
    simpa using h
  · have h := hasSum_choose_mul_geometric_of_norm_lt_one k hw
    rw [one_div] at h
    refine h.congr_fun fun n => ?_
    rw [show k + 1 + n - 1 = n + k by omega, Nat.choose_symm_add]

theorem hasSum_negBinomial_real (m : ℕ) {w : ℝ} (hw : |w| < 1) :
    HasSum (fun n : ℕ => (((m + n - 1).choose n : ℕ) : ℝ) * w ^ n) ((1 - w) ^ m)⁻¹ := by
  have h := hasSum_negBinomial m (w := (w : ℂ)) (by rwa [Complex.norm_real, Real.norm_eq_abs])
  rw [← Complex.hasSum_ofReal]
  push_cast
  exact h

/-! ## The nonnegative double series -/

/-- `c_j z^{2j} C(2j+n-1, n) s^n`. -/
def liClockGermTerm (z s : ℝ) (jn : ℕ × ℕ) : ℝ :=
  liClockThetaGeneratorCoeff jn.1 * z ^ (2 * jn.1) *
    ((((2 * jn.1 + jn.2 - 1).choose jn.2 : ℕ) : ℝ) * s ^ jn.2)

theorem liClockGermTerm_nonneg {z s : ℝ} (hz : 0 ≤ z) (hs : 0 ≤ s) (jn : ℕ × ℕ) :
    0 ≤ liClockGermTerm z s jn := by
  unfold liClockGermTerm
  have := liClockThetaGeneratorCoeff_pos jn.1
  positivity

theorem hasSum_liClockGermTerm_fiber {z s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) (j : ℕ) :
    HasSum (fun n => liClockGermTerm z s (j, n)) (liClockThetaGeneratorCoeff j * (z / (1 - s)) ^ (2 * j)) := by
  have h := (hasSum_negBinomial_real (2 * j) (w := s) (by rwa [abs_of_nonneg hs0])).mul_left
    (liClockThetaGeneratorCoeff j * z ^ (2 * j))
  have e : liClockThetaGeneratorCoeff j * (z / (1 - s)) ^ (2 * j) =
      liClockThetaGeneratorCoeff j * z ^ (2 * j) * ((1 - s) ^ (2 * j))⁻¹ := by
    rw [div_pow]; ring
  rw [e]
  exact h

theorem summable_liClockGermTerm {z s : ℝ} (hz : 0 ≤ z) (hs0 : 0 ≤ s) (hs1 : s < 1) :
    Summable (liClockGermTerm z s) := by
  refine (summable_prod_of_nonneg (fun jn => liClockGermTerm_nonneg hz hs0 jn)).2
    ⟨fun j => (hasSum_liClockGermTerm_fiber hs0 hs1 j).summable, ?_⟩
  refine (summable_liClockThetaGeneratorReal_term (z / (1 - s))).congr fun j => ?_
  exact ((hasSum_liClockGermTerm_fiber hs0 hs1 j).tsum_eq).symm

theorem summable_liClockGermCoeffSeries {z : ℝ} (hz : 0 ≤ z) (n : ℕ) :
    Summable fun j => liClockThetaGeneratorCoeff j * z ^ (2 * j) *
      (((2 * j + n - 1).choose n : ℕ) : ℝ) := by
  have h := (summable_liClockGermTerm (z := z) (s := 1 / 2) hz (by norm_num)
    (by norm_num)).prod_symm.prod_factor n
  refine (h.mul_right (((1 : ℝ) / 2) ^ n)⁻¹).congr fun j => ?_
  simp only [liClockGermTerm, Prod.swap_prod_mk]
  field_simp

/-! ## The coefficients -/

/-- `a_n(z) = z^n/Φ(z) · Σ_j c_j z^{2j} C(2j+n-1, n)`. -/
def liClockReciprocalGermCoeff (z : ℝ) (n : ℕ) : ℝ :=
  z ^ n / Φ z * ∑' j : ℕ, liClockThetaGeneratorCoeff j * z ^ (2 * j) *
    (((2 * j + n - 1).choose n : ℕ) : ℝ)

private theorem Φ_pos (x : ℝ) : 0 < Φ x := lt_of_lt_of_le one_pos (one_le_liClockThetaGeneratorReal x)

theorem liClockReciprocalGermCoeff_zero (z : ℝ) : liClockReciprocalGermCoeff z 0 = 1 := by
  unfold liClockReciprocalGermCoeff
  simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, mul_one, one_div]
  rw [show (∑' j : ℕ, liClockThetaGeneratorCoeff j * z ^ (2 * j)) = Φ z from rfl]
  exact inv_mul_cancel₀ (Φ_pos z).ne'

/-- **Coefficient lower bound (C11).**  `a_n ≥ (ν₁ z²/(2Φ(z))) (n+1) z^n`. -/
theorem liClockReciprocalGermCoeff_ge {z : ℝ} (hz : 0 < z) (n : ℕ) :
    thetaCuspNormalizedEvenMoment 1 * z ^ 2 / (2 * Φ z) * (n + 1) * z ^ n ≤
      liClockReciprocalGermCoeff z n := by
  have hs := summable_liClockGermCoeffSeries hz.le n
  have h1 := le_hasSum hs.hasSum 1 fun j _ => by
    have := liClockThetaGeneratorCoeff_pos j; positivity
  have hc1 : liClockThetaGeneratorCoeff 1 = thetaCuspNormalizedEvenMoment 1 / 2 := by
    simp [liClockThetaGeneratorCoeff, Nat.factorial]
  rw [show 2 * 1 + n - 1 = n + 1 by omega, Nat.choose_succ_self_right, hc1] at h1
  unfold liClockReciprocalGermCoeff
  have hΦ := Φ_pos z
  calc thetaCuspNormalizedEvenMoment 1 * z ^ 2 / (2 * Φ z) * (n + 1) * z ^ n =
      z ^ n / Φ z * (thetaCuspNormalizedEvenMoment 1 / 2 * z ^ (2 * 1) * (((n + 1 : ℕ)) : ℝ)) := by
        push_cast; field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by positivity)

theorem liClockReciprocalGermCoeff_pos {z : ℝ} (hz : 0 < z) (n : ℕ) :
    0 < liClockReciprocalGermCoeff z n := by
  refine lt_of_lt_of_le ?_ (liClockReciprocalGermCoeff_ge hz n)
  have := thetaCuspNormalizedEvenMoment_pos 1
  have := Φ_pos z
  positivity

/-! ## The complete exchange -/

/-- **Raw germ (C7–C8).**  For `|u| < 1/z`, `Φ(z/(1-zu))/Φ(z) = Σ_n a_n(z) u^n` as a complex
germ. -/
theorem hasSum_liClockReciprocalGerm {z : ℝ} (hz : 0 < z) {u : ℂ} (hu : ‖u‖ < 1 / z) :
    HasSum (fun n => (liClockReciprocalGermCoeff z n : ℂ) * u ^ n)
      (liClockThetaGenerator ((z : ℂ) / (1 - z * u)) / Φ z) := by
  set w : ℂ := (z : ℂ) * u
  have hw : ‖w‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hz]
    rwa [lt_div_iff₀ hz, mul_comm] at hu
  set F : ℕ × ℕ → ℂ := fun jn => ((liClockThetaGeneratorCoeff jn.1 * z ^ (2 * jn.1) : ℝ) : ℂ) *
    ((((2 * jn.1 + jn.2 - 1).choose jn.2 : ℕ) : ℂ) * w ^ jn.2)
  have hFs : Summable F := by
    refine Summable.of_norm_bounded (summable_liClockGermTerm hz.le (norm_nonneg w) hw) fun jn => ?_
    simp only [F, liClockGermTerm, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_natCast, abs_of_pos hz, abs_of_pos (liClockThetaGeneratorCoeff_pos jn.1)]
    exact le_rfl
  have hF := hFs.hasSum
  -- fibres over `j`
  have hj : ∀ j, HasSum (fun n => F (j, n)) (((liClockThetaGeneratorCoeff j : ℝ) : ℂ) *
      ((z : ℂ) / (1 - w)) ^ (2 * j)) := by
    intro j
    have h := (hasSum_negBinomial (2 * j) hw).mul_left
      (((liClockThetaGeneratorCoeff j * z ^ (2 * j) : ℝ) : ℂ))
    have e : ((liClockThetaGeneratorCoeff j : ℝ) : ℂ) * ((z : ℂ) / (1 - w)) ^ (2 * j) =
        ((liClockThetaGeneratorCoeff j * z ^ (2 * j) : ℝ) : ℂ) * ((1 - w) ^ (2 * j))⁻¹ := by
      push_cast; rw [div_pow]; ring
    rw [e]
    exact h
  have hΨ : HasSum (fun j => ((liClockThetaGeneratorCoeff j : ℝ) : ℂ) *
      ((z : ℂ) / (1 - w)) ^ (2 * j)) (liClockThetaGenerator ((z : ℂ) / (1 - w))) :=
    (summable_norm_liClockThetaGeneratorTerm _).of_norm.hasSum
  have hS : ∑' jn, F jn = liClockThetaGenerator ((z : ℂ) / (1 - w)) :=
    (hF.prod_fiberwise hj).unique hΨ
  -- fibres over `n`
  have hn : ∀ n, HasSum (fun j => F (j, n))
      (((∑' j : ℕ, liClockThetaGeneratorCoeff j * z ^ (2 * j) *
        (((2 * j + n - 1).choose n : ℕ) : ℝ) : ℝ) : ℂ) * w ^ n) := by
    intro n
    have h := Complex.hasSum_ofReal.2 (summable_liClockGermCoeffSeries hz.le n).hasSum
    have h2 := h.mul_right (w ^ n)
    refine h2.congr_fun fun j => ?_
    simp only [F]
    push_cast
    ring
  have hswap : HasSum (fun p : ℕ × ℕ => F p.swap) (∑' jn, F jn) :=
    (Equiv.prodComm ℕ ℕ).hasSum_iff.2 hF
  have hsum := hswap.prod_fiberwise fun n => hn n
  rw [hS] at hsum
  have hΦ : ((Φ z : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Φ_pos z).ne'
  have hfin := hsum.div_const ((Φ z : ℝ) : ℂ)
  refine hfin.congr_fun fun n => ?_
  unfold liClockReciprocalGermCoeff
  simp only [w]
  push_cast
  field_simp
  ring

/-- The real germ `Q_z(u) = Φ(z/(1-zu))/Φ(z)`. -/
def liClockReciprocalGermReal (z u : ℝ) : ℝ := Φ (z / (1 - z * u)) / Φ z

theorem hasSum_liClockReciprocalGermReal {z : ℝ} (hz : 0 < z) {u : ℝ} (hu : |u| < 1 / z) :
    HasSum (fun n => liClockReciprocalGermCoeff z n * u ^ n) (liClockReciprocalGermReal z u) := by
  have h := hasSum_liClockReciprocalGerm hz (u := (u : ℂ)) (by rwa [Complex.norm_real])
  rw [← Complex.hasSum_ofReal]
  push_cast
  convert h using 1
  unfold liClockReciprocalGermReal
  push_cast
  rw [← liClockThetaGenerator_ofReal]
  push_cast
  rfl

/-! ## The exact radius -/

theorem tendsto_liClockReciprocalGermCoeff_mul_pow_zero {z : ℝ} (hz : 0 < z) {r : ℝ} (hr0 : 0 ≤ r)
    (hr : r < 1 / z) :
    Tendsto (fun n => liClockReciprocalGermCoeff z n * r ^ n) atTop (𝓝 0) :=
  (hasSum_liClockReciprocalGermReal hz (u := r) (by rwa [abs_of_nonneg hr0])).summable.tendsto_atTop_zero

theorem tendsto_liClockReciprocalGermCoeff_mul_pow_atTop {z : ℝ} (hz : 0 < z) {r : ℝ}
    (hr : 1 / z ≤ r) :
    Tendsto (fun n => liClockReciprocalGermCoeff z n * r ^ n) atTop atTop := by
  set C := thetaCuspNormalizedEvenMoment 1 * z ^ 2 / (2 * Φ z)
  have hC : 0 < C := by
    have := thetaCuspNormalizedEvenMoment_pos 1; have := Φ_pos z; positivity
  have hzr : 1 ≤ z * r := by rwa [div_le_iff₀ hz, mul_comm] at hr
  have hr0 : 0 ≤ r := le_trans (by positivity) hr
  refine tendsto_atTop_mono (fun n => ?_) ((tendsto_natCast_atTop_atTop.atTop_add
    (tendsto_const_nhds (x := (1 : ℝ)))).const_mul_atTop hC)
  calc C * ((n : ℝ) + 1) ≤ C * (n + 1) * (z * r) ^ n :=
        le_mul_of_one_le_right (by positivity) (one_le_pow₀ hzr)
    _ = C * (n + 1) * z ^ n * r ^ n := by rw [mul_pow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (liClockReciprocalGermCoeff_ge hz n) (pow_nonneg hr0 n)

/-- **Exact radius (C12).**  The coefficient series has radius exactly `1/z`. -/
theorem radius_liClockReciprocalGermCoeff {z : ℝ} (hz : 0 < z) :
    (FormalMultilinearSeries.ofScalars ℝ (liClockReciprocalGermCoeff z)).radius =
      ENNReal.ofReal (1 / z) := by
  apply le_antisymm
  · by_contra hlt
    push Not at hlt
    obtain ⟨r, hr1, hr2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hlt
    obtain ⟨C, hCpos, hC⟩ := FormalMultilinearSeries.norm_mul_pow_le_of_lt_radius _ hr2
    have hr : 1 / z ≤ (r : ℝ) := by
      have := (ENNReal.ofReal_lt_iff_lt_toReal (by positivity) ENNReal.coe_ne_top).1 hr1
      simpa using this.le
    obtain ⟨n, hn⟩ := ((tendsto_liClockReciprocalGermCoeff_mul_pow_atTop hz hr).eventually
      (eventually_gt_atTop C)).exists
    have := hC n
    rw [FormalMultilinearSeries.ofScalars_norm, Real.norm_eq_abs,
      abs_of_pos (liClockReciprocalGermCoeff_pos hz n)] at this
    linarith
  · refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
    have hr' : (r : ℝ) < 1 / z := by
      have := (ENNReal.lt_ofReal_iff_toReal_lt ENNReal.coe_ne_top).1 hr
      simpa using this
    refine FormalMultilinearSeries.le_radius_of_summable _ ?_
    refine (hasSum_liClockReciprocalGermReal hz (u := r) (by
      rw [NNReal.abs_eq]; exact hr')).summable.congr fun n => ?_
    rw [FormalMultilinearSeries.ofScalars_norm, Real.norm_eq_abs,
      abs_of_pos (liClockReciprocalGermCoeff_pos hz n)]

/-! ## Infinitely many ratio drops -/

/-- **Ratio drops (C13).**  For every `N` some `n ≥ max 1 N` has `a_{n+1}/a_n < a_n/a_{n-1}`. -/
theorem exists_liClockReciprocalGermCoeff_ratio_drop {z : ℝ} (hz : 0 < z) (N : ℕ) :
    ∃ n, max 1 N ≤ n ∧
      liClockReciprocalGermCoeff z (n + 1) / liClockReciprocalGermCoeff z n <
        liClockReciprocalGermCoeff z n / liClockReciprocalGermCoeff z (n - 1) := by
  by_contra hcon
  push Not at hcon
  set a := liClockReciprocalGermCoeff z
  set m := max 1 N
  have hpos : ∀ n, 0 < a n := liClockReciprocalGermCoeff_pos hz
  set q : ℕ → ℝ := fun n => a n / a (n - 1)
  have hq0 : ∀ n, 0 < q n := fun n => div_pos (hpos n) (hpos _)
  have hmono : ∀ n, m ≤ n → q n ≤ q (n + 1) := by
    intro n hn
    have := hcon n hn
    simp only [q, Nat.add_sub_cancel]
    exact this
  have hmono' : ∀ k, m ≤ k → ∀ n, k ≤ n → q k ≤ q n := by
    intro k hk n hn
    induction n, hn using Nat.le_induction with
    | base => exact le_rfl
    | succ n hkn ih => exact ih.trans (hmono n (hk.trans hkn))
  have hstep : ∀ n, a (n + 1) = a n * q (n + 1) := by
    intro n
    simp only [q, Nat.add_sub_cancel]
    field_simp [(hpos n).ne']
  have hm1 : 1 ≤ m := le_max_left _ _
  by_cases hA : ∃ k, m ≤ k ∧ z < q k
  · obtain ⟨k, hkm, hk⟩ := hA
    have hqk := hq0 k
    have hgrow : ∀ n, k ≤ n → a k * q k ^ (n - k) ≤ a n := by
      intro n hn
      induction n, hn using Nat.le_induction with
      | base => simp
      | succ n hkn ih =>
        rw [hstep n, show n + 1 - k = n - k + 1 by omega, pow_succ, ← mul_assoc]
        exact mul_le_mul ih (hmono' k hkm (n + 1) (by omega)) hqk.le (hpos n).le
    set r := (1 / q k + 1 / z) / 2
    have hlt : 1 / q k < 1 / z := one_div_lt_one_div_of_lt hz hk
    have hr1 : 1 / q k < r := by simp only [r]; linarith
    have hr2 : r < 1 / z := by simp only [r]; linarith
    have hr0 : 0 < r := lt_of_le_of_lt (by positivity) hr1
    have hqr : 1 ≤ q k * r := by
      have := (div_lt_iff₀ hqk).1 hr1
      linarith [mul_comm r (q k)]
    have hlow : ∀ n, k ≤ n → a k * r ^ k ≤ a n * r ^ n := by
      intro n hn
      calc a k * r ^ k ≤ a k * r ^ k * (q k * r) ^ (n - k) :=
            le_mul_of_one_le_right (by have := hpos k; positivity) (one_le_pow₀ hqr)
        _ = a k * q k ^ (n - k) * r ^ n := by
            rw [mul_pow, show r ^ n = r ^ k * r ^ (n - k) by rw [← pow_add]; congr 1; omega]
            ring
        _ ≤ a n * r ^ n := mul_le_mul_of_nonneg_right (hgrow n hn) (by positivity)
    have ht := tendsto_liClockReciprocalGermCoeff_mul_pow_zero hz hr0.le hr2
    obtain ⟨n, hn1, hn2⟩ := ((ht.eventually (gt_mem_nhds (show 0 < a k * r ^ k by
      have := hpos k; positivity))).and (eventually_ge_atTop k)).exists
    linarith [hlow n hn2]
  · push Not at hA
    have hdecay : ∀ n, m ≤ n → a n ≤ a m * z ^ (n - m) := by
      intro n hn
      induction n, hn using Nat.le_induction with
      | base => simp
      | succ n hmn ih =>
        rw [hstep n, show n + 1 - m = n - m + 1 by omega, pow_succ, ← mul_assoc]
        exact mul_le_mul ih (hA (n + 1) (by omega)) (hq0 _).le (by have := hpos m; positivity)
    set C := thetaCuspNormalizedEvenMoment 1 * z ^ 2 / (2 * Φ z)
    have hC : 0 < C := by
      have := thetaCuspNormalizedEvenMoment_pos 1; have := Φ_pos z; positivity
    obtain ⟨n, hn⟩ := exists_nat_gt (a m * (1 / z) ^ m / C + m)
    have hmn : m ≤ n := by
      have : (m : ℝ) < n := by
        have : 0 ≤ a m * (1 / z) ^ m / C := by have := hpos m; positivity
        linarith
      exact_mod_cast this.le
    have h1 := liClockReciprocalGermCoeff_ge hz n
    have h2 := hdecay n hmn
    have hzn : z ^ n * (1 / z) ^ n = 1 := by rw [← mul_pow, mul_one_div_cancel hz.ne', one_pow]
    have h3 : C * (n + 1) ≤ a m * (1 / z) ^ m := by
      have e1 : C * (n + 1) = C * (n + 1) * z ^ n * (1 / z) ^ n := by
        rw [mul_assoc (C * (n + 1)), hzn, mul_one]
      have e2 : a m * z ^ (n - m) * (1 / z) ^ n = a m * (1 / z) ^ m := by
        rw [show (1 / z) ^ n = (1 / z) ^ (n - m) * (1 / z) ^ m by rw [← pow_add]; congr 1; omega,
          ← mul_assoc, mul_assoc (a m), ← mul_pow, mul_one_div_cancel hz.ne', one_pow, mul_one]
      calc C * (n + 1) = C * (n + 1) * z ^ n * (1 / z) ^ n := e1
        _ ≤ a n * (1 / z) ^ n := mul_le_mul_of_nonneg_right h1 (by positivity)
        _ ≤ a m * z ^ (n - m) * (1 / z) ^ n := mul_le_mul_of_nonneg_right h2 (by positivity)
        _ = _ := e2
    have h4 : a m * (1 / z) ^ m / C < n := by linarith [show (0 : ℝ) ≤ m from Nat.cast_nonneg m]
    rw [div_lt_iff₀ hC] at h4
    nlinarith

/-! ## The logarithmic germ and the coefficient recurrence -/

theorem hasFPowerSeriesOnBall_liClockReciprocalGermReal {z : ℝ} (hz : 0 < z) :
    HasFPowerSeriesOnBall (liClockReciprocalGermReal z)
      (FormalMultilinearSeries.ofScalars ℝ (liClockReciprocalGermCoeff z)) 0
        (ENNReal.ofReal (1 / z)) where
  r_le := (radius_liClockReciprocalGermCoeff hz).ge
  r_pos := by simpa using hz
  hasSum := by
    intro y hy
    have hy' : |y| < 1 / z := by
      rw [Metric.mem_eball, edist_dist, Real.dist_eq, sub_zero] at hy
      exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).1 hy
    rw [zero_add]
    refine (hasSum_liClockReciprocalGermReal hz hy').congr_fun fun n => ?_
    rw [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]

/-- `a_n(z) = Q_z^{(n)}(0)/n!`. -/
theorem liClockReciprocalGermCoeff_eq_iteratedDeriv {z : ℝ} (hz : 0 < z) (n : ℕ) :
    liClockReciprocalGermCoeff z n = iteratedDeriv n (liClockReciprocalGermReal z) 0 / n.factorial := by
  have hp := (hasFPowerSeriesOnBall_liClockReciprocalGermReal hz).hasFPowerSeriesAt
  have hp' := hp.analyticAt.hasFPowerSeriesAt
  have he := hp.eq_formalMultilinearSeries hp'
  have := congrArg (fun p => FormalMultilinearSeries.coeff p n) he
  simpa [FormalMultilinearSeries.coeff_ofScalars] using this

/-- The logarithmic germ `G_z(u) = log Φ(z/(1-zu)) - log Φ(z)`. -/
def liClockReciprocalLogGerm (z u : ℝ) : ℝ :=
  liClockThetaLogGenerator (z / (1 - z * u)) - liClockThetaLogGenerator z

theorem liClockReciprocalGermReal_eq_exp (z : ℝ) :
    liClockReciprocalGermReal z = fun u => Real.exp (liClockReciprocalLogGerm z u) := by
  funext u
  unfold liClockReciprocalGermReal liClockReciprocalLogGerm liClockThetaLogGenerator
  rw [Real.exp_sub, Real.exp_log (Φ_pos _), Real.exp_log (Φ_pos _)]

/-- **Logarithmic germ (C9).**  `log Q_z(u) = H(p - u) - H(p)`, `p = 1/z`. -/
theorem liClockReciprocalLogGerm_eq {z : ℝ} (hz : 0 < z) (u : ℝ) :
    liClockReciprocalLogGerm z u =
      Real.log (Φ (z⁻¹ - u)⁻¹) - Real.log (Φ z⁻¹⁻¹) := by
  unfold liClockReciprocalLogGerm liClockThetaLogGenerator
  have e : (z⁻¹ - u)⁻¹ = z / (1 - z * u) := by
    rw [show z⁻¹ - u = (1 - z * u) / z by field_simp, inv_div]
  rw [inv_inv, e]

theorem log_liClockReciprocalGermReal {z : ℝ} (u : ℝ) :
    Real.log (liClockReciprocalGermReal z u) = liClockReciprocalLogGerm z u := by
  rw [liClockReciprocalGermReal_eq_exp, Real.log_exp]

private theorem contDiffAt_moebius {z : ℝ} : ContDiffAt ℝ ∞ (fun u : ℝ => z / (1 - z * u)) 0 :=
  contDiffAt_const.div (contDiffAt_const.sub (contDiffAt_const.mul contDiffAt_id)) (by simp)

theorem contDiffAt_liClockReciprocalLogGerm (z : ℝ) :
    ContDiffAt ℝ ∞ (liClockReciprocalLogGerm z) 0 :=
  (contDiff_liClockThetaLogGenerator.contDiffAt.comp 0 contDiffAt_moebius).sub contDiffAt_const

/-- The logarithmic coefficients `b_n = G_z^{(n)}(0)/n!`. -/
def liClockReciprocalLogCoeff (z : ℝ) (n : ℕ) : ℝ :=
  iteratedDeriv n (liClockReciprocalLogGerm z) 0 / n.factorial

/-- **Logarithmic coefficients (C9).**  `b_n = (-1)^n H^{(n)}(p)/n!` for `n ≥ 1`, `p = 1/z`. -/
theorem liClockReciprocalLogCoeff_eq {z : ℝ} (hz : 0 < z) {n : ℕ} (hn : 1 ≤ n) :
    liClockReciprocalLogCoeff z n =
      (-1) ^ n * iteratedDeriv n (fun q => Real.log (Φ q⁻¹)) z⁻¹ / n.factorial := by
  have hfun : liClockReciprocalLogGerm z = fun u => Real.log (Φ (z⁻¹ - u)⁻¹) - Real.log (Φ z⁻¹⁻¹) :=
    funext (liClockReciprocalLogGerm_eq hz)
  have hH : ContDiffAt ℝ n (fun u : ℝ => Real.log (Φ (z⁻¹ - u)⁻¹)) 0 := by
    have hinv : ContDiffAt ℝ ∞ (fun u : ℝ => (z⁻¹ - u)⁻¹) 0 :=
      (contDiffAt_const.sub contDiffAt_id).inv (by simpa using hz.ne')
    exact ((contDiff_liClockThetaLogGenerator.contDiffAt.comp 0 hinv).of_le (by exact_mod_cast le_top))
  unfold liClockReciprocalLogCoeff
  rw [hfun, iteratedDeriv_fun_sub hH contDiffAt_const, iteratedDeriv_const,
    if_neg (by omega), sub_zero]
  have := congrFun (iteratedDeriv_comp_const_sub (n := n) (f := fun q => Real.log (Φ q⁻¹))
    (s := z⁻¹)) 0
  simp only [sub_zero, smul_eq_mul] at this
  rw [this]

/-- **Logarithmic coefficients via the Lah sums.**  `b_n = z^n L_n(z)/n!`. -/
theorem liClockReciprocalLogCoeff_eq_lah {z : ℝ} (hz : 0 < z) {n : ℕ} (hn : 1 ≤ n) :
    liClockReciprocalLogCoeff z n =
      z ^ n * lahCumulantSum liClockThetaLogGenerator n z / n.factorial := by
  rw [liClockReciprocalLogCoeff_eq hz hn,
    neg_one_pow_mul_iteratedDeriv_log_inv_eq_lahCumulantSum n hz]

/-- **Coefficient recurrence (C10).**  `(n+1) a_{n+1} = Σ_{k ≤ n} (k+1) b_{k+1} a_{n-k}`. -/
theorem liClockReciprocalGermCoeff_recurrence {z : ℝ} (hz : 0 < z) (n : ℕ) :
    (n + 1) * liClockReciprocalGermCoeff z (n + 1) =
      ∑ k ∈ Finset.range (n + 1), (k + 1) * liClockReciprocalLogCoeff z (k + 1) *
        liClockReciprocalGermCoeff z (n - k) := by
  have hQexp := liClockReciprocalGermReal_eq_exp z
  have hG := contDiffAt_liClockReciprocalLogGerm z
  have hQ : ContDiffAt ℝ ∞ (liClockReciprocalGermReal z) 0 := by
    rw [hQexp]
    exact Real.contDiff_exp.contDiffAt.comp 0 hG
  have hG' : ContDiffAt ℝ n (deriv (liClockReciprocalLogGerm z)) 0 :=
    hG.derivWithin (by exact_mod_cast le_top)
  have hderiv : deriv (liClockReciprocalGermReal z) =ᶠ[𝓝 0]
      liClockReciprocalGermReal z * deriv (liClockReciprocalLogGerm z) := by
    filter_upwards [(hG.of_le (show (1 : WithTop ℕ∞) ≤ ∞ by exact_mod_cast le_top)).eventually
      (by simp)] with u hu
    have hd : DifferentiableAt ℝ (liClockReciprocalLogGerm z) u := hu.differentiableAt one_ne_zero
    rw [hQexp, Pi.mul_apply]
    exact hd.hasDerivAt.exp.deriv
  set G := liClockReciprocalLogGerm z
  set Q := liClockReciprocalGermReal z
  have hlhs : iteratedDeriv (n + 1) Q 0 =
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * iteratedDeriv i Q 0 *
        iteratedDeriv (n - i + 1) G 0 := by
    rw [iteratedDeriv_succ', hderiv.iteratedDeriv_eq n,
      iteratedDeriv_mul (hQ.of_le (by exact_mod_cast le_top)) hG']
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← iteratedDeriv_succ']
  have hfac : ∀ i, iteratedDeriv i Q 0 = (i.factorial : ℝ) * liClockReciprocalGermCoeff z i := by
    intro i
    rw [liClockReciprocalGermCoeff_eq_iteratedDeriv hz]
    field_simp
    rfl
  have hfacG : ∀ k, iteratedDeriv k G 0 = (k.factorial : ℝ) * liClockReciprocalLogCoeff z k := by
    intro k
    unfold liClockReciprocalLogCoeff
    field_simp
    rfl
  have hn1 : ((n + 1).factorial : ℝ) * liClockReciprocalGermCoeff z (n + 1) =
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ((i.factorial : ℝ) *
        liClockReciprocalGermCoeff z i) * (((n - i + 1).factorial : ℝ) *
          liClockReciprocalLogCoeff z (n - i + 1)) := by
    rw [← hfac, hlhs]
    exact Finset.sum_congr rfl fun i _ => by rw [hfac, hfacG]
  have hnf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hterm : ∀ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ((i.factorial : ℝ) *
      liClockReciprocalGermCoeff z i) * (((n - i + 1).factorial : ℝ) *
        liClockReciprocalLogCoeff z (n - i + 1)) =
      (n.factorial : ℝ) * ((((n - i : ℕ) : ℝ) + 1) * liClockReciprocalLogCoeff z (n - i + 1) *
        liClockReciprocalGermCoeff z i) := by
    intro i hi
    have hin : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have hc := Nat.choose_mul_factorial_mul_factorial hin
    rw [Nat.factorial_succ (n - i)]
    have hc' : (n.choose i : ℝ) * (i.factorial : ℝ) * ((n - i).factorial : ℝ) = n.factorial := by
      exact_mod_cast hc
    push_cast
    linear_combination (((n - i : ℕ) : ℝ) + 1) * liClockReciprocalLogCoeff z (n - i + 1) *
      liClockReciprocalGermCoeff z i * hc'
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, Nat.factorial_succ] at hn1
  push_cast at hn1
  have hn2 : (n + 1) * liClockReciprocalGermCoeff z (n + 1) =
      ∑ i ∈ Finset.range (n + 1), (((n - i : ℕ) : ℝ) + 1) * liClockReciprocalLogCoeff z (n - i + 1) *
        liClockReciprocalGermCoeff z i := by
    have := hn1
    rw [show ((n : ℝ) + 1) * (n.factorial : ℝ) * liClockReciprocalGermCoeff z (n + 1) =
      (n.factorial : ℝ) * ((n + 1) * liClockReciprocalGermCoeff z (n + 1)) by ring] at this
    exact mul_left_cancel₀ hnf.ne' this
  rw [hn2, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
  rw [show n + 1 - 1 - k = n - k by omega, show n - (n - k) = k by omega]

end RHTower
