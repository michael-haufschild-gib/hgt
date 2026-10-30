import GaloisForLFunctions.RHTower.XiSliceKKLScaleOffLineDetection

/-!
# The heat detection rate is quadratic in the depth

Let `f_t(y) = |ξ(½+y+it)|²`, let `T_n(λ, 0, t)` be the heated slice coefficients, and let
`H(y) = E f_t(y + √λ Z)` be the heated slice on the positive axis (`heatedSliceReal`).

**Theorem** (`re_xiSliceHeatTransfer_neg_of_slice_zero_quadratic`).  For `t ≥ e^{1600}`, every
off-line zero `½ + δ + it` and every `κ ∈ (0, δ²/200]`, some `T_n(κ/log t, 0, t)` has negative real
part.

This removes the factor `log(3/δ)` from the rate `δ²/(200(log(3/δ) + 1))` of
`re_xiSliceHeatTransfer_neg_of_slice_zero`, and the rate is uniform in `δ`.

Proof.  Suppose every `a_n = Re T_n` is `≥ 0`, so `H(y) = Σ a_n yⁿ`.

* **Log-convexity** (`hasSum_le_rpow_mul_rpow`).  For a nonnegative power series,
  `H(r₁^{1−θ} r₂^θ) ≤ H(r₁)^{1−θ} H(r₂)^θ`: weighted AM–GM term by term.
* **Local degree** (`heatedSliceReal_le_pow_mul_half`).  Three radii give
  `H(δ/2) ≥ (δ/3)^M f_t(3/2)/4` with `M ≍ log t`, and the envelope gives
  `H(3/2) ≤ √2 f_t(3/2) e^{3A/2 + 9/2 + 2A²λ}`.  Interpolating between `δ/2` and `3/2`, the deficit
  `(3/δ)^M` at `δ/2` becomes `(2R/δ)^M` at radius `R`:
  `H(R) ≤ D (2R/δ)^M H(δ/2)` for `δ/2 ≤ R ≤ 3/2`.  The loss depends on `R/δ` only.
* **Relative growth** (`heatedSliceReal_le_relative_growth`).  With `x ≤ e^{x/e}` this becomes
  `H(R) ≤ D H(δ/2) e^{(A + 2M/(eδ))R + 2R²}` for all `R > 0`.
* **Hermite tail** (`re_xiSliceHeatTransfer_neg_of_relative_growth`).  The zero at `δ` forces
  `H(δ/2) ≤ 6D e^{c₁}(2/3)^{⌊δ²/(4λ)⌋+1} H(δ/2)`, impossible once `δ²/λ ≫ log t`, that is
  `κ ≤ δ²/200`.

The corpus loss `log(3/δ)` came from comparing `H(δ/2)` with `f_t(3/2)` directly.  The quadratic
loss itself is the cluster loss: a cluster of `≍ log t` zeros within `δ` of `½ + it` gives local degree
`≍ log t` at radius `δ`, against `≍ δ log t` for regularly spaced zeros
(`re_xiSliceHeatTransfer_neg_of_regular_growth`).
-/

open MeasureTheory Filter Topology

namespace RHTower

noncomputable section

/-! ## Log-convexity of nonnegative power series -/

/-- **Log-convexity.**  If `a_n ≥ 0`, `Σ a_n r₁ⁿ = G₁ > 0`, `Σ a_n r₂ⁿ = G₂ > 0` and `0 ≤ θ ≤ 1`, then
`Σ a_n (r₁^{1−θ} r₂^θ)ⁿ ≤ G₁^{1−θ} G₂^θ`. -/
theorem hasSum_le_rpow_mul_rpow {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) {r₁ r₂ G₁ G₂ G θ : ℝ}
    (hr₁ : 0 ≤ r₁) (hr₂ : 0 ≤ r₂) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hG₁ : 0 < G₁) (hG₂ : 0 < G₂)
    (h₁ : HasSum (fun n => a n * r₁ ^ n) G₁) (h₂ : HasSum (fun n => a n * r₂ ^ n) G₂)
    (h : HasSum (fun n => a n * (r₁ ^ (1 - θ) * r₂ ^ θ) ^ n) G) :
    G ≤ G₁ ^ (1 - θ) * G₂ ^ θ := by
  set K := G₁ ^ (1 - θ) * G₂ ^ θ with hK
  have hK0 : 0 ≤ K := by positivity
  have hθ' : 0 ≤ 1 - θ := by linarith
  have hterm : ∀ n, a n * (r₁ ^ (1 - θ) * r₂ ^ θ) ^ n
      ≤ K * ((1 - θ) * (a n * r₁ ^ n / G₁) + θ * (a n * r₂ ^ n / G₂)) := by
    intro n
    set u := a n * r₁ ^ n with hu
    set v := a n * r₂ ^ n with hv
    have hu0 : 0 ≤ u := mul_nonneg (ha n) (pow_nonneg hr₁ n)
    have hv0 : 0 ≤ v := mul_nonneg (ha n) (pow_nonneg hr₂ n)
    -- the term is `u^{1−θ} v^θ`
    have hsplit : a n * (r₁ ^ (1 - θ) * r₂ ^ θ) ^ n = u ^ (1 - θ) * v ^ θ := by
      rw [hu, hv, Real.mul_rpow (ha n) (pow_nonneg hr₁ n), Real.mul_rpow (ha n) (pow_nonneg hr₂ n),
        ← Real.rpow_natCast_mul hr₁, ← Real.rpow_natCast_mul hr₂, mul_pow,
        ← Real.rpow_mul_natCast hr₁, ← Real.rpow_mul_natCast hr₂]
      have ha1 : a n = a n ^ (1 - θ) * a n ^ θ := by
        rw [← Real.rpow_add' (ha n) (by norm_num), sub_add_cancel, Real.rpow_one]
      conv_lhs => rw [ha1]
      rw [mul_comm (1 - θ) (n : ℝ), mul_comm θ (n : ℝ)]
      ring
    have hamgm := Real.geom_mean_le_arith_mean2_weighted hθ' hθ0 (div_nonneg hu0 hG₁.le)
      (div_nonneg hv0 hG₂.le) (by ring)
    rw [Real.div_rpow hu0 hG₁.le, Real.div_rpow hv0 hG₂.le] at hamgm
    have hG₁θ : 0 < G₁ ^ (1 - θ) := Real.rpow_pos_of_pos hG₁ _
    have hG₂θ : 0 < G₂ ^ θ := Real.rpow_pos_of_pos hG₂ _
    rw [hsplit, hK]
    have e : u ^ (1 - θ) / G₁ ^ (1 - θ) * (v ^ θ / G₂ ^ θ)
        = u ^ (1 - θ) * v ^ θ / (G₁ ^ (1 - θ) * G₂ ^ θ) := by
      field_simp
    rw [e, div_le_iff₀ (mul_pos hG₁θ hG₂θ)] at hamgm
    linarith
  have hsum : HasSum (fun n => K * ((1 - θ) * (a n * r₁ ^ n / G₁) + θ * (a n * r₂ ^ n / G₂)))
      (K * ((1 - θ) * (G₁ / G₁) + θ * (G₂ / G₂))) :=
    (((h₁.div_const G₁).mul_left (1 - θ)).add ((h₂.div_const G₂).mul_left θ)).mul_left K
  have hle := hasSum_le hterm h hsum
  rw [div_self hG₁.ne', div_self hG₂.ne'] at hle
  linarith

/-! ## The local degree of the heated slice -/

/-- The heated slice `H(y) = (2π)^{−1/2} ∫ e^{−w²/2} f_t(√λ w + y) dw`. -/
def heatedSliceReal (t lam y : ℝ) : ℝ :=
  (∫ w : ℝ, Real.exp (-(w ^ 2 / 2)) * xiSliceReal t (Real.sqrt lam * w + y))
    / Real.sqrt (2 * Real.pi)

/-- The local-degree constant `D = 4√2 e^{3A/2 + 9/2 + 2A²λ}`, `A = log t + K₀`. -/
def heatLocalDegreeConstant (t lam : ℝ) : ℝ :=
  4 * Real.sqrt 2 * Real.exp (3 / 2 * (Real.log t + xiSliceGlobalConstant) + 9 / 2
    + 2 * (Real.log t + xiSliceGlobalConstant) ^ 2 * lam)

/-- The local degree `M = ⌈(3A + 20 + 2A²λ)/log 2⌉` of the three-radii bound. -/
def heatLocalDegree (t lam : ℝ) : ℕ :=
  ⌈(3 * (Real.log t + xiSliceGlobalConstant) + 20
    + 2 * (Real.log t + xiSliceGlobalConstant) ^ 2 * lam) / Real.log 2⌉₊

theorem one_le_heatLocalDegreeConstant {t lam : ℝ} (ht : 16 ≤ t) (hlam : 0 ≤ lam) :
    1 ≤ heatLocalDegreeConstant t lam := by
  unfold heatLocalDegreeConstant
  have hA : 0 ≤ Real.log t + xiSliceGlobalConstant :=
    add_nonneg (Real.log_nonneg (by linarith)) xiSliceGlobalConstant_pos.le
  have h1 : 1 ≤ Real.exp (3 / 2 * (Real.log t + xiSliceGlobalConstant) + 9 / 2
      + 2 * (Real.log t + xiSliceGlobalConstant) ^ 2 * lam) := Real.one_le_exp (by positivity)
  have h2 : 1 ≤ Real.sqrt 2 := Real.one_le_sqrt.mpr (by norm_num)
  nlinarith

theorem hasSum_heatedSliceReal {t lam y : ℝ} (hlam : 0 < lam) (hy : 0 < y) :
    HasSum (fun n => (DeBruijn.xiSliceHeatTransfer lam 0 t n).re * y ^ n) (heatedSliceReal t lam y) :=
  hasSum_re_xiSliceHeatTransfer_mul_pow hlam hy

/-- Under absolute monotonicity the heated slice is nondecreasing on `(0, ∞)`. -/
theorem heatedSliceReal_mono {t lam y₁ y₂ : ℝ} (hlam : 0 < lam) (hy₁ : 0 < y₁) (h12 : y₁ ≤ y₂)
    (hAM : ∀ n, 0 ≤ (DeBruijn.xiSliceHeatTransfer lam 0 t n).re) :
    heatedSliceReal t lam y₁ ≤ heatedSliceReal t lam y₂ :=
  hasSum_le (fun n => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hy₁.le h12 n) (hAM n))
    (hasSum_heatedSliceReal hlam hy₁) (hasSum_heatedSliceReal hlam (hy₁.trans_le h12))

/-- **Envelope.**  For `t ≥ 16`, `16λ ≤ 1` and `R ≥ 0`, `H(R) ≤ √2 f_t(3/2) e^{AR + 2R² + 2A²λ}`. -/
theorem heatedSliceReal_le_envelope {t lam R : ℝ} (ht : 16 ≤ t) (hlam : 0 < lam)
    (hlam16 : 16 * lam ≤ 1) (hR : 0 ≤ R) :
    heatedSliceReal t lam R ≤ Real.sqrt 2 * xiSliceReal t (3 / 2)
      * Real.exp ((Real.log t + xiSliceGlobalConstant) * R + 2 * R ^ 2
        + 2 * (Real.log t + xiSliceGlobalConstant) ^ 2 * lam) := by
  obtain ⟨-, hUR⟩ := integral_gauss_mul_xiSliceReal_le (R := R) ht hlam hlam16 hR
  have hs2π : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have e : Real.sqrt (4 * Real.pi) = Real.sqrt 2 * Real.sqrt (2 * Real.pi) := by
    rw [← Real.sqrt_mul (by norm_num)]; congr 1; ring
  rw [e] at hUR
  unfold heatedSliceReal
  rw [div_le_iff₀ hs2π]
  refine hUR.trans (le_of_eq ?_)
  ring

/-- **Local degree of the heated slice.**  Let `t ≥ 16`, `16λ ≤ 1`, `0 < δ ≤ 1`, and let every
`Re T_n(λ, 0, t)` be `≥ 0`.  For `δ/2 ≤ R ≤ 3/2`,
`H(R) ≤ D (2R/δ)^M H(δ/2)` with `D = heatLocalDegreeConstant t λ`, `M = heatLocalDegree t λ`. -/
theorem heatedSliceReal_le_pow_mul_half {t lam δ R : ℝ} (ht : 16 ≤ t) (hlam : 0 < lam)
    (hlam16 : 16 * lam ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hR1 : δ / 2 ≤ R) (hR2 : R ≤ 3 / 2)
    (hAM : ∀ n, 0 ≤ (DeBruijn.xiSliceHeatTransfer lam 0 t n).re) :
    heatedSliceReal t lam R
      ≤ heatLocalDegreeConstant t lam * (2 * R / δ) ^ heatLocalDegree t lam
        * heatedSliceReal t lam (δ / 2) := by
  set A := Real.log t + xiSliceGlobalConstant with hA
  set M := heatLocalDegree t lam with hM
  set D := heatLocalDegreeConstant t lam with hD
  set F := xiSliceReal t (3 / 2) with hF
  set G := heatedSliceReal t lam (δ / 2) with hG
  set P := heatedSliceReal t lam (3 / 2) with hP
  have hF0 : 0 < F := xiSliceReal_pos t (by norm_num)
  have hδ2 : 0 < δ / 2 := by positivity
  have hR0 : 0 < R := hδ2.trans_le hR1
  -- the two endpoint bounds
  have hlow : (δ / 3) ^ M * (F / 4) ≤ G := heatSeries_half_ge ht hlam hlam16 hδ (by linarith) hAM
  have hG0 : 0 < G := lt_of_lt_of_le (by positivity) hlow
  have hFG : F ≤ 4 * (3 / δ) ^ M * G := by
    have h3 : (3 / δ) ^ M * (δ / 3) ^ M = 1 := by
      rw [← mul_pow, div_mul_div_comm, mul_comm 3 δ, div_self (by positivity), one_pow]
    have := mul_le_mul_of_nonneg_left hlow (show 0 ≤ 4 * (3 / δ) ^ M by positivity)
    calc F = 4 * ((3 / δ) ^ M * (δ / 3) ^ M) * (F / 4) := by rw [h3]; ring
      _ = 4 * (3 / δ) ^ M * ((δ / 3) ^ M * (F / 4)) := by ring
      _ ≤ 4 * (3 / δ) ^ M * G := this
  have hPD : P ≤ D * (3 / δ) ^ M * G := by
    have h := heatedSliceReal_le_envelope ht hlam hlam16 (show (0 : ℝ) ≤ 3 / 2 by norm_num)
    rw [← hA] at h
    have e : Real.exp (A * (3 / 2) + 2 * (3 / 2) ^ 2 + 2 * A ^ 2 * lam)
        = Real.exp (3 / 2 * A + 9 / 2 + 2 * A ^ 2 * lam) := by congr 1; ring
    rw [e] at h
    calc P ≤ Real.sqrt 2 * F * Real.exp (3 / 2 * A + 9 / 2 + 2 * A ^ 2 * lam) := h
      _ ≤ Real.sqrt 2 * (4 * (3 / δ) ^ M * G) * Real.exp (3 / 2 * A + 9 / 2 + 2 * A ^ 2 * lam) := by
          gcongr
      _ = D * (3 / δ) ^ M * G := by rw [hD, heatLocalDegreeConstant, ← hA]; ring
  -- the interpolation exponent
  have hl3 : 0 < Real.log (3 / δ) := Real.log_pos (by rw [lt_div_iff₀ hδ]; linarith)
  set θ := Real.log (2 * R / δ) / Real.log (3 / δ) with hθ
  have h2R : 1 ≤ 2 * R / δ := by rw [le_div_iff₀ hδ]; linarith
  have hθ0 : 0 ≤ θ := div_nonneg (Real.log_nonneg h2R) hl3.le
  have hθ1 : θ ≤ 1 := by
    rw [hθ, div_le_one hl3]
    exact Real.log_le_log (by positivity) (by rw [div_le_div_iff_of_pos_right hδ]; linarith)
  have h3θ : (3 / δ) ^ θ = 2 * R / δ := by
    rw [Real.rpow_def_of_pos (by positivity), hθ, mul_div_cancel₀ _ hl3.ne',
      Real.exp_log (by positivity)]
  have hRθ : (δ / 2) ^ (1 - θ) * (3 / 2) ^ θ = R := by
    have e : (3 / 2 : ℝ) = (δ / 2) * (3 / δ) := by field_simp
    rw [e, Real.mul_rpow hδ2.le (by positivity), h3θ, ← mul_assoc,
      ← Real.rpow_add hδ2, sub_add_cancel, Real.rpow_one]
    field_simp
  -- log-convexity between `δ/2` and `3/2`
  have hP0 : 0 < P := hG0.trans_le (heatedSliceReal_mono hlam hδ2 (by linarith) hAM)
  have hconv : heatedSliceReal t lam R ≤ G ^ (1 - θ) * P ^ θ := by
    have h := hasSum_le_rpow_mul_rpow hAM hδ2.le (by norm_num : (0 : ℝ) ≤ 3 / 2) hθ0 hθ1 hG0 hP0
      (hasSum_heatedSliceReal hlam hδ2) (hasSum_heatedSliceReal hlam (by norm_num))
      (G := heatedSliceReal t lam R) (by rw [hRθ]; exact hasSum_heatedSliceReal hlam hR0)
    exact h
  have hD1 : 1 ≤ D := one_le_heatLocalDegreeConstant ht hlam.le
  calc heatedSliceReal t lam R ≤ G ^ (1 - θ) * P ^ θ := hconv
    _ ≤ G ^ (1 - θ) * (D * (3 / δ) ^ M * G) ^ θ := by gcongr
    _ = D ^ θ * ((3 / δ) ^ θ) ^ M * (G ^ (1 - θ) * G ^ θ) := by
        rw [Real.mul_rpow (by positivity) hG0.le, Real.mul_rpow (by positivity) (by positivity),
          ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
          ← Real.rpow_mul (by positivity), mul_comm (M : ℝ) θ]
        ring
    _ = D ^ θ * (2 * R / δ) ^ M * G := by
        rw [h3θ, ← Real.rpow_add hG0, sub_add_cancel, Real.rpow_one]
    _ ≤ D * (2 * R / δ) ^ M * G := by
        gcongr
        calc D ^ θ ≤ D ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hD1 hθ1
          _ = D := Real.rpow_one D

/-- `x ≤ e^{x/e}` for every real `x`. -/
theorem le_exp_div_exp_one (x : ℝ) : x ≤ Real.exp (x / Real.exp 1) := by
  have h := Real.add_one_le_exp (x / Real.exp 1 - 1)
  rw [sub_add_cancel, Real.exp_sub] at h
  rwa [le_div_iff₀ (Real.exp_pos 1), div_mul_cancel₀ _ (Real.exp_pos 1).ne'] at h

/-- **Relative growth from the local degree.**  Under the hypotheses of
`heatedSliceReal_le_pow_mul_half`, for every `R > 0`,
`H(R) ≤ D H(δ/2) e^{(A + 2M/(eδ))R + 2R²}`. -/
theorem heatedSliceReal_le_relative_growth {t lam δ R : ℝ} (ht : 16 ≤ t) (hlam : 0 < lam)
    (hlam16 : 16 * lam ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hR : 0 < R)
    (hAM : ∀ n, 0 ≤ (DeBruijn.xiSliceHeatTransfer lam 0 t n).re) :
    heatedSliceReal t lam R
      ≤ heatLocalDegreeConstant t lam * heatedSliceReal t lam (δ / 2)
        * Real.exp (((Real.log t + xiSliceGlobalConstant)
          + 2 * heatLocalDegree t lam / (Real.exp 1 * δ)) * R + 2 * R ^ 2) := by
  set A := Real.log t + xiSliceGlobalConstant with hA
  set M := heatLocalDegree t lam with hM
  set D := heatLocalDegreeConstant t lam with hD
  set G := heatedSliceReal t lam (δ / 2) with hG
  have hA0 : 0 ≤ A := add_nonneg (Real.log_nonneg (by linarith)) xiSliceGlobalConstant_pos.le
  have hD1 : 1 ≤ D := one_le_heatLocalDegreeConstant ht hlam.le
  have hδ2 : 0 < δ / 2 := by positivity
  have hG0 : 0 ≤ G := (hasSum_heatedSliceReal hlam hδ2).nonneg fun n =>
    mul_nonneg (hAM n) (pow_nonneg hδ2.le n)
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  -- `(2R/δ)^M ≤ e^{2MR/(eδ)}`
  have hpow : (2 * R / δ) ^ M ≤ Real.exp (2 * M / (Real.exp 1 * δ) * R) := by
    have h := le_exp_div_exp_one (2 * R / δ)
    calc (2 * R / δ) ^ M ≤ Real.exp (2 * R / δ / Real.exp 1) ^ M :=
          pow_le_pow_left₀ (by positivity) h M
      _ = Real.exp (2 * M / (Real.exp 1 * δ) * R) := by
          rw [← Real.exp_nat_mul]; congr 1; field_simp
  have hexp_mono : Real.exp (2 * M / (Real.exp 1 * δ) * R)
      ≤ Real.exp ((A + 2 * M / (Real.exp 1 * δ)) * R + 2 * R ^ 2) := by
    refine Real.exp_le_exp.mpr ?_
    have : 0 ≤ A * R := mul_nonneg hA0 hR.le
    nlinarith [sq_nonneg R]
  rcases lt_or_ge R (δ / 2) with hsmall | hbig
  · -- below `δ/2`: monotonicity
    have h := heatedSliceReal_mono hlam hR hsmall.le hAM
    have h1 : 1 ≤ Real.exp ((A + 2 * M / (Real.exp 1 * δ)) * R + 2 * R ^ 2) :=
      Real.one_le_exp (by positivity)
    calc heatedSliceReal t lam R ≤ G := h
      _ = 1 * G * 1 := by ring
      _ ≤ D * G * Real.exp ((A + 2 * M / (Real.exp 1 * δ)) * R + 2 * R ^ 2) := by gcongr
  rcases le_or_gt R (3 / 2) with hmid | hlarge
  · -- between `δ/2` and `3/2`: the local degree
    have h := heatedSliceReal_le_pow_mul_half ht hlam hlam16 hδ hδ1 hbig hmid hAM
    calc heatedSliceReal t lam R ≤ D * (2 * R / δ) ^ M * G := h
      _ ≤ D * Real.exp ((A + 2 * M / (Real.exp 1 * δ)) * R + 2 * R ^ 2) * G := by
          gcongr; exact hpow.trans hexp_mono
      _ = _ := by ring
  · -- beyond `3/2`: the envelope and three radii
    set F := xiSliceReal t (3 / 2) with hF
    have hlow : (δ / 3) ^ M * (F / 4) ≤ G :=
      heatSeries_half_ge ht hlam hlam16 hδ (by linarith) hAM
    have hFG : F ≤ 4 * (3 / δ) ^ M * G := by
      have h3 : (3 / δ) ^ M * (δ / 3) ^ M = 1 := by
        rw [← mul_pow, div_mul_div_comm, mul_comm 3 δ, div_self (by positivity), one_pow]
      have := mul_le_mul_of_nonneg_left hlow (show 0 ≤ 4 * (3 / δ) ^ M by positivity)
      calc F = 4 * ((3 / δ) ^ M * (δ / 3) ^ M) * (F / 4) := by rw [h3]; ring
        _ = 4 * (3 / δ) ^ M * ((δ / 3) ^ M * (F / 4)) := by ring
        _ ≤ 4 * (3 / δ) ^ M * G := this
    have h3R : (3 / δ) ^ M ≤ (2 * R / δ) ^ M :=
      pow_le_pow_left₀ (by positivity) (by rw [div_le_div_iff_of_pos_right hδ]; linarith) M
    have henv := heatedSliceReal_le_envelope ht hlam hlam16 hR.le
    rw [← hA] at henv
    have hexpA : Real.exp (A * R + 2 * R ^ 2 + 2 * A ^ 2 * lam)
        ≤ Real.exp (3 / 2 * A + 9 / 2 + 2 * A ^ 2 * lam) * Real.exp (A * R + 2 * R ^ 2) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by nlinarith)
    have hDexp : 4 * Real.sqrt 2 * Real.exp (3 / 2 * A + 9 / 2 + 2 * A ^ 2 * lam) = D := by
      rw [hD, heatLocalDegreeConstant, ← hA]
    calc heatedSliceReal t lam R
        ≤ Real.sqrt 2 * F * Real.exp (A * R + 2 * R ^ 2 + 2 * A ^ 2 * lam) := henv
      _ ≤ Real.sqrt 2 * (4 * (2 * R / δ) ^ M * G)
          * (Real.exp (3 / 2 * A + 9 / 2 + 2 * A ^ 2 * lam) * Real.exp (A * R + 2 * R ^ 2)) := by
          gcongr
          exact hFG.trans (by gcongr)
      _ = D * G * ((2 * R / δ) ^ M * Real.exp (A * R + 2 * R ^ 2)) := by rw [← hDexp]; ring
      _ ≤ D * G * (Real.exp (2 * M / (Real.exp 1 * δ) * R) * Real.exp (A * R + 2 * R ^ 2)) := by
          gcongr
      _ = D * G * Real.exp ((A + 2 * M / (Real.exp 1 * δ)) * R + 2 * R ^ 2) := by
          rw [← Real.exp_add]; congr 2; ring

/-! ## Detection at the quadratic rate -/

/-- **Detection of an off-line zero at heat `δ²/(200 log t)`.**  For `t ≥ e^{1600}`, `δ > 0` with
`f_t(δ) = 0` (an off-line zero `½ + δ + it`) and `κ ∈ (0, δ²/200]`, some heated slice coefficient
`T_n(κ/log t, 0, t)` has negative real part. -/
theorem re_xiSliceHeatTransfer_neg_of_slice_zero_quadratic {t : ℝ} (ht : Real.exp 1600 ≤ t)
    {δ : ℝ} (hδ : 0 < δ) (hzero : xiSliceReal t δ = 0) {κ : ℝ} (hκ : 0 < κ)
    (hκδ : κ ≤ δ ^ 2 / 200) :
    ∃ n : ℕ, (DeBruijn.xiSliceHeatTransfer (κ / Real.log t) 0 t n).re < 0 := by
  by_contra hcon
  push Not at hcon
  -- sizes
  have hδ2 : δ ≤ 1 / 2 := by
    by_contra h
    push Not at h
    exact (xiSliceReal_pos t h).ne' hzero
  set L := Real.log t with hLdef
  have hL : 1600 ≤ L := by
    rw [hLdef, ← Real.log_exp 1600]; exact Real.log_le_log (Real.exp_pos _) ht
  have ht16 : 16 ≤ t := by
    have h1 : (16 : ℝ) ≤ Real.exp 1600 := by
      have := Real.add_one_le_exp (1600 : ℝ); linarith
    linarith
  have hK0 := xiSliceGlobalConstant_pos
  have hK16 := xiSliceGlobalConstant_le_sixteen
  set A := L + xiSliceGlobalConstant with hA
  have hκδ' : 200 * κ ≤ δ ^ 2 := by linarith
  have hδsq : δ ^ 2 ≤ 1 / 4 := by nlinarith
  have hκ800 : κ ≤ 1 / 800 := by linarith
  set lam := κ / L with hlamdef
  have hL0 : 0 < L := by linarith
  have hlam : 0 < lam := div_pos hκ hL0
  have hlamL : lam * L = κ := by rw [hlamdef]; field_simp
  have hlam512 : 512 * lam ≤ 1 := by
    rw [hlamdef, mul_div_assoc', div_le_one hL0]; linarith
  -- the relative growth bound
  set M := heatLocalDegree t lam with hM
  set D := heatLocalDegreeConstant t lam with hD
  set α := A + 2 * M / (Real.exp 1 * δ) with hα
  have hgr : ∀ R : ℝ, 0 < R →
      (∫ w : ℝ, Real.exp (-(w ^ 2 / 2)) * xiSliceReal t (Real.sqrt lam * w + R))
          / Real.sqrt (2 * Real.pi)
        ≤ D * ((∫ w : ℝ, Real.exp (-(w ^ 2 / 2)) * xiSliceReal t (Real.sqrt lam * w + δ / 2))
          / Real.sqrt (2 * Real.pi)) * Real.exp (α * R + 2 * R ^ 2) := fun R hR =>
    heatedSliceReal_le_relative_growth ht16 hlam (by linarith) hδ (by linarith) hR hcon
  have hD0 : 0 < D := lt_of_lt_of_le one_pos (one_le_heatLocalDegreeConstant ht16 hlam.le)
  obtain ⟨n, hn⟩ := re_xiSliceHeatTransfer_neg_of_relative_growth ht16 hlam (by linarith) hδ hzero
    hD0 (by norm_num : (0 : ℝ) ≤ 2) (by linarith) hgr ?_
  · exact absurd (hcon n) (not_le.mpr hn)
  -- the numerical condition `log(6D) + 2αδ + 16δ² + 32α²λ < (δ²/(4λ)) log(3/2)`
  have hA1 : A ≤ 101 / 100 * L := by rw [hA]; linarith
  have hAL : L ≤ A := by rw [hA]; linarith
  have hA2lam : A ^ 2 * lam ≤ L / 700 := by
    have h1 : A ^ 2 ≤ (101 / 100 * L) ^ 2 := pow_le_pow_left₀ (by linarith) hA1 2
    have h2 : A ^ 2 * lam ≤ (101 / 100 * L) ^ 2 * lam := mul_le_mul_of_nonneg_right h1 hlam.le
    have h3 : (101 / 100 * L) ^ 2 * lam = (101 / 100) ^ 2 * L * κ := by rw [← hlamL]; ring
    have h4 : (101 / 100) ^ 2 * L * κ ≤ (101 / 100) ^ 2 * L * (1 / 800) :=
      mul_le_mul_of_nonneg_left hκ800 (by positivity)
    nlinarith
  have hl2 : 69 / 100 ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hMle : (M : ℝ) ≤ 443 / 100 * L := by
    set X := 3 * A + 20 + 2 * A ^ 2 * lam with hX
    have hX0 : 0 ≤ X := by positivity
    have h1 : (M : ℝ) < X / Real.log 2 + 1 := by
      rw [hM, heatLocalDegree, ← hLdef, ← hA]; exact Nat.ceil_lt_add_one (by positivity)
    have h2 : X / Real.log 2 ≤ X / (69 / 100) := div_le_div_of_nonneg_left hX0 (by norm_num) hl2
    have h3 : X ≤ 305 / 100 * L := by rw [hX]; linarith
    have h4 : X / (69 / 100) ≤ 305 / 100 * L / (69 / 100) :=
      div_le_div_of_nonneg_right h3 (by norm_num)
    have h5 : 305 / 100 * L / (69 / 100) = 305 / 69 * L := by ring
    linarith
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  -- `log(6D) ≤ 4 + 3A/2 + 9/2 + 2A²λ`
  have he1 := Real.exp_one_gt_d9
  have hlogD : Real.log (6 * D) ≤ 4 + (3 / 2 * A + 9 / 2 + 2 * A ^ 2 * lam) := by
    rw [Real.log_le_iff_le_exp (by positivity), Real.exp_add, hD, heatLocalDegreeConstant, ← hLdef,
      ← hA]
    have hs : Real.sqrt 2 ≤ 3 / 2 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
    have h4 : (36 : ℝ) ≤ Real.exp 4 := by
      have e : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
      rw [e]
      have : (2.7182818283 : ℝ) ^ 4 ≤ Real.exp 1 ^ 4 := pow_le_pow_left₀ (by norm_num) he1.le 4
      nlinarith
    have hE := Real.exp_pos (3 / 2 * A + 9 / 2 + 2 * A ^ 2 * lam)
    nlinarith
  -- `2αδ = 2Aδ + 4M/e`
  have hαδ : 2 * α * δ ≤ A + 4 * M / (27 / 10) := by
    have e : 2 * α * δ = 2 * A * δ + 4 * M / Real.exp 1 := by rw [hα]; field_simp
    have h1 : 4 * M / Real.exp 1 ≤ 4 * M / (27 / 10) :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
    have h2 : 2 * A * δ ≤ A := by nlinarith
    linarith
  -- `32α²λ ≤ 64A²λ + 64q²λ` with `q = 2M/(eδ)` and `q²λ ≤ 4M²/(1458 L)`
  set q := 2 * M / (Real.exp 1 * δ) with hq
  have hα2 : 32 * α ^ 2 * lam ≤ 64 * (A ^ 2 * lam) + 64 * (q ^ 2 * lam) := by
    have : α ^ 2 ≤ 2 * A ^ 2 + 2 * q ^ 2 := by rw [hα]; nlinarith [sq_nonneg (A - q)]
    nlinarith
  have hqlam : q ^ 2 * lam ≤ 4 * M ^ 2 / (1458 * L) := by
    have e : q ^ 2 * lam = (2 * M) ^ 2 * κ / ((Real.exp 1 * δ) ^ 2 * L) := by
      rw [hq, hlamdef]; field_simp
    rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
    have he2 : 729 / 100 ≤ Real.exp 1 ^ 2 := by nlinarith
    have h1 : 1458 * κ ≤ Real.exp 1 ^ 2 * δ ^ 2 := by nlinarith
    have h2 : 0 ≤ 4 * M ^ 2 * L := by positivity
    nlinarith
  have hM2 : 4 * M ^ 2 / (1458 * L) ≤ 54 / 1000 * L := by
    rw [div_le_iff₀ (by positivity)]
    have : (M : ℝ) ^ 2 ≤ (443 / 100 * L) ^ 2 := pow_le_pow_left₀ hM0 hMle 2
    nlinarith
  -- the right side is at least `50L/3`
  have hl32 : (1 : ℝ) / 3 ≤ Real.log (3 / 2) := by
    have := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 3 / 2 by norm_num)
    norm_num at this ⊢; linarith
  have hrhs : 50 * L / 3 ≤ δ ^ 2 / (4 * lam) * Real.log (3 / 2) := by
    have h1 : 50 * L ≤ δ ^ 2 / (4 * lam) := by
      rw [le_div_iff₀ (by positivity)]
      have : 50 * L * (4 * lam) = 200 * κ := by rw [← hlamL]; ring
      linarith
    have h2 := mul_le_mul h1 hl32 (by norm_num) (by positivity)
    linarith
  have h16 : 8 * 2 * δ ^ 2 ≤ 4 := by linarith
  have h4M : 4 * M / (27 / 10) ≤ 4 * (443 / 100 * L) / (27 / 10) :=
    div_le_div_of_nonneg_right (by linarith) (by norm_num)
  linarith

end

end RHTower
