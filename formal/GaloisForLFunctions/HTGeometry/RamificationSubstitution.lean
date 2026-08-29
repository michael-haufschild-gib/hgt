import GaloisForLFunctions.HTGeometry.LogDerivCountingRatio
import GaloisForLFunctions.HTGeometry.BorelGoodRadii
import GaloisForLFunctions.HTGeometry.ZeroFreeRadius

/-!
# The Borel substitution in the logarithmic-derivative estimate

At a Borel-good radius `r` the characteristic does not double across the step `1/T(r)`.  Choosing the
Poisson–Jensen radii inside that step — `R` in `(r + 1/(4T), r + 1/(2T))`, avoiding the countably many
radii whose circle carries a zero, and `R' = r + 1/T` — makes every quantity in the estimate of
`circleAverage_posLog_logDeriv_le_counting_ratio` polynomial in `r` and `T(r)`.

The resulting bound has exactly the shape that `eventually_le_of_log_poly_bound_const` turns into
`o(T(r))`.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Metric Real ValueDistribution MeromorphicOn Set

/-- `u/(1+u) ≤ log (1 + u)` for `u ≥ 0`. -/
theorem log_one_add_ge {u : ℝ} (hu : 0 ≤ u) : u / (1 + u) ≤ Real.log (1 + u) := by
  have h1 : (0 : ℝ) < 1 + u := by linarith
  have h2 := Real.log_le_sub_one_of_pos (x := (1 + u)⁻¹) (by positivity)
  rw [Real.log_inv] at h2
  have h3 : (1 + u)⁻¹ - 1 = -(u / (1 + u)) := by
    field_simp
    ring
  rw [h3] at h2
  linarith

/-- `y^{1/2} ≤ y + 1` for `y ≥ 0`. -/
theorem rpow_half_le_add_one {y : ℝ} (hy : 0 ≤ y) : y ^ (1 / 2 : ℝ) ≤ y + 1 := by
  rcases le_or_gt y 1 with h | h
  · calc y ^ (1 / 2 : ℝ) ≤ (1 : ℝ) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow hy h (by norm_num)
      _ = 1 := Real.one_rpow _
      _ ≤ y + 1 := by linarith
  · calc y ^ (1 / 2 : ℝ) ≤ y ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le h.le (by norm_num)
      _ = y := Real.rpow_one y
      _ ≤ y + 1 := by linarith

/-- `y^{1/2} ≤ y` for `y ≥ 1`. -/
theorem rpow_half_le_self {y : ℝ} (hy : 1 ≤ y) : y ^ (1 / 2 : ℝ) ≤ y := by
  calc y ^ (1 / 2 : ℝ) ≤ y ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hy (by norm_num)
    _ = y := Real.rpow_one y


/-- At a Borel-good radius, the reciprocal of the ratio loss is at most `4 (r+1) / t`. -/
theorem inv_log_ratio_le {r t R : ℝ} (hr : 1 ≤ r) (ht0 : 0 < t) (ht1 : t ≤ 1)
    (hRlow : r + t / 4 < R) (hRhigh : R < r + t / 2) :
    (Real.log ((r + t) / R))⁻¹ ≤ 4 * (r + 1) / t := by
  have hRpos : 0 < R := by linarith
  have hRle : R ≤ r + 1 := by linarith
  set x : ℝ := (r + t - R) / R with hxdef
  have hnum : t / 2 < r + t - R := by linarith
  have hx0 : 0 < x := by
    rw [hxdef]
    apply div_pos (by linarith) hRpos
  have hxle : x ≤ 1 := by
    rw [hxdef, div_le_one hRpos]
    linarith
  have hratio : (r + t) / R = 1 + x := by
    rw [hxdef]
    field_simp
    ring
  have hlow : t / (2 * (r + 1)) ≤ x := by
    rw [hxdef, le_div_iff₀ hRpos]
    have hstep : t / (2 * (r + 1)) * R ≤ t / (2 * (r + 1)) * (r + 1) := by
      refine mul_le_mul_of_nonneg_left hRle (by positivity)
    have hcancel : t / (2 * (r + 1)) * (r + 1) = t / 2 := by
      field_simp
    linarith [hstep, hcancel, hnum]
  have hlogge : t / (4 * (r + 1)) ≤ Real.log ((r + t) / R) := by
    rw [hratio]
    have hstep := log_one_add_ge hx0.le
    have hhalf : x / 2 ≤ x / (1 + x) := by
      refine div_le_div_of_nonneg_left hx0.le (by linarith) (by linarith)
    have hlow2 : t / (4 * (r + 1)) ≤ x / 2 := by
      have : t / (2 * (r + 1)) / 2 = t / (4 * (r + 1)) := by
        field_simp
        ring
      calc t / (4 * (r + 1)) = t / (2 * (r + 1)) / 2 := this.symm
        _ ≤ x / 2 := by linarith
    linarith [hstep, hhalf, hlow2]
  have hlogpos : 0 < Real.log ((r + t) / R) := by
    have : (0 : ℝ) < t / (4 * (r + 1)) := by positivity
    linarith
  rw [inv_le_comm₀ hlogpos (by positivity)]
  have heq : (4 * (r + 1) / t)⁻¹ = t / (4 * (r + 1)) := by
    rw [inv_div]
  rw [heq]
  exact hlogge


/-- The explicit value of the Poisson–Jensen coefficient at the substituted radii. -/
theorem coefB_value (r T : ℝ) (hT : T ≠ 0) :
    2 * (r + 1) / ((T⁻¹) / 4) ^ 2 = 32 * (r + 1) * T ^ 2 := by
  field_simp
  ring

/-- The arithmetic core of the substitution: three factor bounds combine into one polynomial. -/
theorem substitution_poly_bound {A1 A2 A3 r T M κ p : ℝ}
    (hr : 1 ≤ r) (hT : 1 ≤ T) (hM : 0 ≤ M) (hκ : 0 ≤ κ) (hp : 0 < p)
    (hA1 : A1 ≤ 4 * (r + 1) * T * (2 * T + M)) (hA10 : 0 ≤ A1)
    (hA2 : A2 ≤ κ + 4 * p * T) (hA20 : 0 ≤ A2)
    (hA3 : A3 ≤ 32 * (r + 1) * T ^ 2 * (4 * T + M) + 1) :
    (2 * p)⁻¹ * (A1 * A2) + A3
      ≤ ((2 * p)⁻¹ * (4 * (4 + M)) * (κ + 4 * p) + 32 * (4 + M) + 1)
        * (r + 1) ^ 4 * (T + 1) ^ 4 := by
  have hr1 : (1 : ℝ) ≤ r + 1 := by linarith
  have hT1 : (1 : ℝ) ≤ T + 1 := by linarith
  have hstep1 : T * (2 * T + M) ≤ (4 + M) * (T + 1) ^ 2 := by nlinarith [hT, hM]
  have h1 : A1 ≤ 4 * (4 + M) * (r + 1) * (T + 1) ^ 2 := by
    have hmul : 4 * (r + 1) * (T * (2 * T + M)) ≤ 4 * (r + 1) * ((4 + M) * (T + 1) ^ 2) :=
      mul_le_mul_of_nonneg_left hstep1 (by linarith)
    nlinarith [hA1, hmul]
  have h2 : A2 ≤ (κ + 4 * p) * (T + 1) := by
    have hκT : (0 : ℝ) ≤ κ * T := mul_nonneg hκ (by linarith)
    have hexpand : (κ + 4 * p) * (T + 1) = κ * T + κ + 4 * p * T + 4 * p := by ring
    linarith only [hA2, hκT, hp, hexpand.le, hexpand.ge]
  have hT0' : (0 : ℝ) ≤ T := by linarith
  have hMT3 : (0 : ℝ) ≤ M * T ^ 3 := mul_nonneg hM (by positivity)
  have hMT2 : (0 : ℝ) ≤ M * T ^ 2 := mul_nonneg hM (by positivity)
  have hMT : (0 : ℝ) ≤ M * T := mul_nonneg hM hT0'
  have hstep3 : T ^ 2 * (4 * T + M) ≤ (4 + M) * (T + 1) ^ 3 := by
    nlinarith [hT, hM, hMT3, hMT2, hMT, hT0']
  have hcube : (1 : ℝ) ≤ (T + 1) ^ 3 := one_le_pow₀ hT1
  have hone : (1 : ℝ) ≤ (r + 1) * (T + 1) ^ 3 := by nlinarith [hr1, hcube]
  have h3 : A3 ≤ (32 * (4 + M) + 1) * (r + 1) * (T + 1) ^ 3 := by
    have hmul : 32 * (r + 1) * (T ^ 2 * (4 * T + M))
        ≤ 32 * (r + 1) * ((4 + M) * (T + 1) ^ 3) :=
      mul_le_mul_of_nonneg_left hstep3 (by linarith)
    nlinarith [hA3, hmul, hone]
  have hprod : A1 * A2 ≤ (4 * (4 + M) * (r + 1) * (T + 1) ^ 2) * ((κ + 4 * p) * (T + 1)) :=
    mul_le_mul h1 h2 hA20 (by positivity)
  have hinvp : (0 : ℝ) < (2 * p)⁻¹ := by positivity
  have hscaled : (2 * p)⁻¹ * (A1 * A2)
      ≤ (2 * p)⁻¹ * ((4 * (4 + M) * (r + 1) * (T + 1) ^ 2) * ((κ + 4 * p) * (T + 1))) :=
    mul_le_mul_of_nonneg_left hprod hinvp.le
  have hcollect : (2 * p)⁻¹ * ((4 * (4 + M) * (r + 1) * (T + 1) ^ 2) * ((κ + 4 * p) * (T + 1)))
      + (32 * (4 + M) + 1) * (r + 1) * (T + 1) ^ 3
      = ((2 * p)⁻¹ * (4 * (4 + M)) * (κ + 4 * p) + 32 * (4 + M) + 1)
        * ((r + 1) * (T + 1) ^ 3) := by ring
  have hgrow : ((2 * p)⁻¹ * (4 * (4 + M)) * (κ + 4 * p) + 32 * (4 + M) + 1)
      * ((r + 1) * (T + 1) ^ 3)
      ≤ ((2 * p)⁻¹ * (4 * (4 + M)) * (κ + 4 * p) + 32 * (4 + M) + 1)
        * (r + 1) ^ 4 * (T + 1) ^ 4 := by
    have hC0 : (0 : ℝ) ≤ (2 * p)⁻¹ * (4 * (4 + M)) * (κ + 4 * p) + 32 * (4 + M) + 1 := by
      positivity
    have hfac : (r + 1) * (T + 1) ^ 3 ≤ (r + 1) ^ 4 * (T + 1) ^ 4 := by
      have h3' : (1 : ℝ) ≤ (r + 1) ^ 3 := one_le_pow₀ hr1
      have hexp : (r + 1) ^ 4 = (r + 1) * (r + 1) ^ 3 := by ring
      have ha : (r + 1) ≤ (r + 1) ^ 4 := by
        rw [hexp]
        nlinarith [h3', hr1]
      have hb : (T + 1) ^ 3 ≤ (T + 1) ^ 4 := pow_le_pow_right₀ hT1 (by omega)
      have hb0 : (0 : ℝ) ≤ (T + 1) ^ 3 := by positivity
      have ha0 : (0 : ℝ) ≤ (r + 1) ^ 4 := by positivity
      calc (r + 1) * (T + 1) ^ 3 ≤ (r + 1) ^ 4 * (T + 1) ^ 3 :=
            mul_le_mul_of_nonneg_right ha hb0
        _ ≤ (r + 1) ^ 4 * (T + 1) ^ 4 := mul_le_mul_of_nonneg_left hb ha0
    calc ((2 * p)⁻¹ * (4 * (4 + M)) * (κ + 4 * p) + 32 * (4 + M) + 1) * ((r + 1) * (T + 1) ^ 3)
        ≤ ((2 * p)⁻¹ * (4 * (4 + M)) * (κ + 4 * p) + 32 * (4 + M) + 1)
          * ((r + 1) ^ 4 * (T + 1) ^ 4) := mul_le_mul_of_nonneg_left hfac hC0
      _ = ((2 * p)⁻¹ * (4 * (4 + M)) * (κ + 4 * p) + 32 * (4 + M) + 1)
          * (r + 1) ^ 4 * (T + 1) ^ 4 := by ring
  linarith [hscaled, h3, hcollect.le, hcollect.ge, hgrow]

/-- **The Borel substitution.**  At a Borel-good radius the logarithmic-derivative estimate becomes
twice the logarithm of a polynomial in the radius and the characteristic majorant. -/
theorem exists_logDeriv_poly_bound {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hf0 : ∀ z, meromorphicOrderAt f z ≠ ⊤) (U : ℝ → ℝ) (hUmono : Monotone U)
    (hU1 : ∀ s, 1 ≤ U s) (hUdom : ∀ s, 1 ≤ s → characteristic f ⊤ s ≤ U s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 1 ≤ r →
      U (r + (U r)⁻¹) < 2 * U r →
      (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..(2 * π),
          Real.posLog ‖logDeriv f ((r : ℂ) * Complex.exp (θ * Complex.I))‖
        ≤ 2 * Real.log (1 + C * (r + 1) ^ 4 * (U r + 1) ^ 4) := by
  classical
  have hana : AnalyticOnNhd ℂ f Set.univ := fun z _ => hf.analyticAt z
  have hfm : Meromorphic f := fun z => (hf.analyticAt z).meromorphicAt
  set κ : ℝ := sinNegPowerConst (1 / 2) with hκdef
  have hκ0 : 0 ≤ κ := sinNegPowerConst_nonneg _
  set M₀ : ℝ := max |Real.log ‖f 0‖| |Real.log ‖meromorphicTrailingCoeffAt f 0‖| with hM₀def
  have hM₀0 : 0 ≤ M₀ := le_trans (abs_nonneg _) (le_max_left _ _)
  have hπ : (0 : ℝ) < π := Real.pi_pos
  refine ⟨(2 * π)⁻¹ * (4 * (4 + M₀)) * (κ + 4 * π) + 32 * (4 + M₀) + 1, by positivity, ?_⟩
  intro r hr hgood
  set T : ℝ := U r with hTdef
  have hT1 : 1 ≤ T := hU1 r
  have hT0 : (0 : ℝ) < T := by linarith
  set t : ℝ := T⁻¹ with htdef
  have ht0 : 0 < t := by positivity
  have ht1 : t ≤ 1 := by
    rw [htdef]
    exact inv_le_one_of_one_le₀ hT1
  obtain ⟨R, hRmem, hRzero⟩ := exists_radius_no_zero_on_sphere hf hf0
    (a := r + t / 4) (b := r + t / 2) (by linarith)
  obtain ⟨hRlow, hRhigh⟩ := hRmem
  have hrpos : (0 : ℝ) < r := by linarith
  have hrR : r < R := by linarith
  have hR1 : 1 ≤ R := by linarith
  have hRpos : (0 : ℝ) < R := by linarith
  have hRR' : R < r + t := by linarith
  have hRle : R ≤ r + 1 := by linarith
  have hR'1 : (1 : ℝ) ≤ r + t := by linarith
  have hbd := divisor_eq_zero_on_sphere hf hf0 hRpos hRzero
  have hmain := circleAverage_posLog_logDeriv_le_counting_ratio (α := 1 / 2)
    (by norm_num) (by norm_num) hrpos hrR hR1 hRR' hf hf0 hbd
  rw [← hκdef, ← hM₀def] at hmain
  have hNtop : logCounting f ⊤ (r + t) = 0 := by
    have h := GaloisForLFunctions.Nevanlinna.logCounting_top_eq_zero_of_analyticOnNhd hana
    rw [h]
    rfl
  have hcharR' : characteristic f ⊤ (r + t) < 2 * T := by
    have h1 : characteristic f ⊤ (r + t) ≤ U (r + t) := hUdom (r + t) hR'1
    linarith [h1, hgood]
  have hN0 : logCounting f 0 (r + t) ≤ 2 * T + M₀ := by
    have hsplit : characteristic f 0 (r + t)
        = proximity f 0 (r + t) + logCounting f 0 (r + t) := rfl
    have hprox : (0 : ℝ) ≤ proximity f 0 (r + t) := proximity_nonneg (r + t)
    have hinv : characteristic f 0 = characteristic f⁻¹ ⊤ := by
      rw [ValueDistribution.characteristic, ValueDistribution.characteristic,
        ValueDistribution.proximity_inv, ValueDistribution.logCounting_inv]
    have hfmt := ValueDistribution.characteristic_sub_characteristic_inv_le
      (f := f) (R := r + t) hfm
    have h1 := (abs_le.mp hfmt).1
    have h3 : characteristic f 0 (r + t) = characteristic f⁻¹ ⊤ (r + t) := by rw [hinv]
    linarith [hsplit, hprox, h1, h3, hcharR']
  have hNsum : logCounting f ⊤ (r + t) + logCounting f 0 (r + t) ≤ 2 * T + M₀ := by
    rw [hNtop]
    linarith [hN0]
  have hNsum0 : (0 : ℝ) ≤ logCounting f ⊤ (r + t) + logCounting f 0 (r + t) := by
    have h1 : (0 : ℝ) ≤ logCounting f ⊤ (r + t) := logCounting_nonneg hR'1
    have h2 : (0 : ℝ) ≤ logCounting f 0 (r + t) := logCounting_nonneg hR'1
    linarith
  have hinvlog : (Real.log ((r + t) / R))⁻¹ ≤ 4 * (r + 1) / t :=
    inv_log_ratio_le hr ht0 ht1 hRlow hRhigh
  have hinvlog0 : (0 : ℝ) ≤ (Real.log ((r + t) / R))⁻¹ := by
    have hlogpos : 0 < Real.log ((r + t) / R) := by
      refine Real.log_pos ?_
      rw [lt_div_iff₀ hRpos]
      linarith
    positivity
  have htT : 4 * (r + 1) / t = 4 * (r + 1) * T := by
    rw [htdef]
    field_simp
  -- the three factors
  have hA1 : (Real.log ((r + t) / R))⁻¹
      * (logCounting f ⊤ (r + t) + logCounting f 0 (r + t))
      ≤ 4 * (r + 1) * T * (2 * T + M₀) := by
    rw [← htT]
    exact mul_le_mul hinvlog hNsum hNsum0 (by positivity)
  have hrhalf : r ^ (-(1 / 2 : ℝ)) ≤ 1 := by
    refine Real.rpow_le_one_of_one_le_of_nonpos hr (by norm_num)
  have hRmr : t / 4 < R - r := by linarith
  have hRmrpos : (0 : ℝ) < R - r := by linarith
  have hA2 : r ^ (-(1 / 2 : ℝ)) * κ
      + 2 * π * (R - r) ^ (-(1 / 2 : ℝ)) ≤ κ + 4 * π * T := by
    have h1 : r ^ (-(1 / 2 : ℝ)) * κ ≤ κ := by
      calc r ^ (-(1 / 2 : ℝ)) * κ ≤ 1 * κ := mul_le_mul_of_nonneg_right hrhalf hκ0
        _ = κ := one_mul κ
    have h2 : (R - r) ^ (-(1 / 2 : ℝ)) ≤ 2 * T := by
      have hstep : (R - r) ^ (-(1 / 2 : ℝ)) ≤ (t / 4) ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hRmr.le (by norm_num)
      have hval : (t / 4) ^ (-(1 / 2 : ℝ)) = (4 * T) ^ (1 / 2 : ℝ) := by
        have hrw : (t / 4 : ℝ) = (4 * T)⁻¹ := by
          rw [htdef]
          field_simp
        rw [hrw, Real.rpow_neg (by positivity), Real.inv_rpow (by positivity), inv_inv]
      have hfin : (4 * T) ^ (1 / 2 : ℝ) ≤ 2 * T := by
        have h4T : (1 : ℝ) ≤ 4 * T := by linarith
        have hsq : ((2 * T) : ℝ) ^ (2 : ℕ) = 4 * T ^ (2 : ℕ) := by ring
        calc (4 * T) ^ (1 / 2 : ℝ) ≤ (4 * T ^ (2 : ℕ)) ^ (1 / 2 : ℝ) := by
              refine Real.rpow_le_rpow (by positivity) ?_ (by norm_num)
              nlinarith [hT1]
          _ = 2 * T := by
              rw [← hsq, ← Real.rpow_natCast (2 * T) 2, ← Real.rpow_mul (by positivity)]
              norm_num
      linarith [hstep, hval.le, hval.ge, hfin]
    have hπ0 : (0 : ℝ) ≤ 2 * π := by positivity
    nlinarith [h1, h2, hπ0]
  -- the third factor
  have hr1' : (1 : ℝ) ≤ r + 1 := by linarith
  have hT1' : (1 : ℝ) ≤ T + 1 := by linarith
  have hcharR : characteristic f ⊤ R < 2 * T := by
    have h1 : characteristic f ⊤ R ≤ U R := hUdom R hR1
    have h2 : U R ≤ U (r + t) := hUmono (by linarith)
    linarith [h1, h2, hgood]
  have hchar0 : (0 : ℝ) ≤ characteristic f ⊤ R := by
    have h1 : (0 : ℝ) ≤ proximity f ⊤ R := proximity_nonneg R
    have h2 : (0 : ℝ) ≤ logCounting f ⊤ R := logCounting_nonneg hR1
    have hsp : characteristic f ⊤ R = proximity f ⊤ R + logCounting f ⊤ R := rfl
    linarith
  set X : ℝ := characteristic f ⊤ R with hXdef
  have hRmrpos2 : (0 : ℝ) < (R - r) ^ 2 := pow_pos (by linarith only [hRmr, ht0]) 2
  have htq : (0 : ℝ) < (t / 4) ^ 2 := pow_pos (by linarith only [ht0]) 2
  have hcoefB : 2 * R / (R - r) ^ 2 ≤ 32 * (r + 1) * T ^ 2 := by
    have hsq : (t / 4) ^ 2 ≤ (R - r) ^ 2 :=
      pow_le_pow_left₀ (by linarith only [ht0]) hRmr.le 2
    have hnum : 2 * R ≤ 2 * (r + 1) := by linarith only [hRle]
    have hstep : 2 * R / (R - r) ^ 2 ≤ 2 * (r + 1) / (t / 4) ^ 2 := by
      gcongr
      all_goals first
        | linarith only [hr, hRhigh, ht1]
        | exact htq
        | linarith only [hRle]
    have hval : 2 * (r + 1) / (t / 4) ^ 2 = 32 * (r + 1) * T ^ 2 := by
      rw [htdef]
      exact coefB_value r T (ne_of_gt hT0)
    linarith only [hstep, hval.le, hval.ge]
  have hcoef0 : (0 : ℝ) ≤ 2 * R / (R - r) ^ 2 :=
    div_nonneg (by linarith only [hRpos]) hRmrpos2.le
  have hinner0 : (0 : ℝ) ≤ 2 * X + M₀ := by linarith only [hchar0, hM₀0]
  have hBbase : (0 : ℝ) ≤ 2 * R / (R - r) ^ 2 * (2 * X + M₀) := mul_nonneg hcoef0 hinner0
  have hA3 : (2 * R / (R - r) ^ 2 * (2 * X + M₀)) ^ (1 / 2 : ℝ)
      ≤ 32 * (r + 1) * T ^ 2 * (4 * T + M₀) + 1 := by
    have hinner : 2 * X + M₀ ≤ 4 * T + M₀ := by linarith only [hcharR]
    have hrhs0 : (0 : ℝ) ≤ 32 * (r + 1) * T ^ 2 := by positivity
    have hprod : 2 * R / (R - r) ^ 2 * (2 * X + M₀) ≤ 32 * (r + 1) * T ^ 2 * (4 * T + M₀) :=
      mul_le_mul hcoefB hinner hinner0 hrhs0
    calc (2 * R / (R - r) ^ 2 * (2 * X + M₀)) ^ (1 / 2 : ℝ)
        ≤ (32 * (r + 1) * T ^ 2 * (4 * T + M₀)) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow hBbase hprod (by norm_num)
      _ ≤ 32 * (r + 1) * T ^ 2 * (4 * T + M₀) + 1 := by
          refine rpow_half_le_add_one ?_
          have h4 : (0 : ℝ) ≤ 4 * T + M₀ := by linarith only [hT1, hM₀0]
          exact mul_nonneg hrhs0 h4
  have hA10 : (0 : ℝ) ≤ (Real.log ((r + t) / R))⁻¹
      * (logCounting f ⊤ (r + t) + logCounting f 0 (r + t)) := mul_nonneg hinvlog0 hNsum0
  have hA20 : (0 : ℝ) ≤ r ^ (-(1 / 2 : ℝ)) * κ + 2 * π * (R - r) ^ (-(1 / 2 : ℝ)) := by
    have h1 : (0 : ℝ) ≤ r ^ (-(1 / 2 : ℝ)) * κ :=
      mul_nonneg (Real.rpow_nonneg (by linarith only [hr]) _) hκ0
    have h2 : (0 : ℝ) ≤ 2 * π * (R - r) ^ (-(1 / 2 : ℝ)) :=
      mul_nonneg (by linarith only [hπ]) (Real.rpow_nonneg (by linarith only [hRmr, ht0]) _)
    linarith only [h1, h2]
  have hpoly := substitution_poly_bound (r := r) (T := T) (M := M₀) (κ := κ) (p := π)
    hr hT1 hM₀0 hκ0 hπ hA1 hA10 hA2 hA20 hA3
  refine le_trans hmain ?_
  have hhalf : (1 : ℝ) / (1 / 2 : ℝ) = 2 := by norm_num
  rw [hhalf]
  refine mul_le_mul_of_nonneg_left (Real.log_le_log ?_ (by linarith only [hpoly])) (by norm_num)
  have hX0 : (0 : ℝ) ≤ (2 * π)⁻¹
      * (((Real.log ((r + t) / R))⁻¹
          * (logCounting f ⊤ (r + t) + logCounting f 0 (r + t)))
        * (r ^ (-(1 / 2 : ℝ)) * κ + 2 * π * (R - r) ^ (-(1 / 2 : ℝ))))
      + (2 * R / (R - r) ^ 2 * (2 * X + M₀)) ^ (1 / 2 : ℝ) := by
    have h1 : (0 : ℝ) ≤ (2 * π)⁻¹ := by positivity
    have h2 : (0 : ℝ) ≤ ((Real.log ((r + t) / R))⁻¹
        * (logCounting f ⊤ (r + t) + logCounting f 0 (r + t)))
        * (r ^ (-(1 / 2 : ℝ)) * κ + 2 * π * (R - r) ^ (-(1 / 2 : ℝ))) := mul_nonneg hA10 hA20
    have h3 : (0 : ℝ) ≤ (2 * R / (R - r) ^ 2 * (2 * X + M₀)) ^ (1 / 2 : ℝ) :=
      Real.rpow_nonneg hBbase _
    have h4 : (0 : ℝ) ≤ (2 * π)⁻¹ * (((Real.log ((r + t) / R))⁻¹
        * (logCounting f ⊤ (r + t) + logCounting f 0 (r + t)))
        * (r ^ (-(1 / 2 : ℝ)) * κ + 2 * π * (R - r) ^ (-(1 / 2 : ℝ)))) := mul_nonneg h1 h2
    linarith only [h3, h4]
  linarith only [hX0]

end GaloisForLFunctions.HTGeometry
