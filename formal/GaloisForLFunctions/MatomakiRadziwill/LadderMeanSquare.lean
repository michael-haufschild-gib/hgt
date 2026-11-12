import GaloisForLFunctions.MatomakiRadziwill.LadderBound

/-!
# Matomäki–Radziwiłł in mean square for `λχ`

For a non-principal Dirichlet character `χ` and every `ε > 0` there is `L₀` such that for every
`L ≥ L₀` (`h = e^L`) there is `X₀` with (`exists_mean_square_twLiouville_le`)

`∫_{|w| ≤ W} |Σ_{X < n ≤ 4X} λ(n)χ(n)/n · n^{2πiw}|² dw ≤ ε`   for `X ≥ X₀`, `W ≤ X e^{-L/2}`.

The bound of the concrete ladder (`ladder_rough_le`, `ladder_nonrough_le`), with Route T giving
`ρ = (log X)^{-3}` on the top scale, is `ladderHPart L + ladderXPart X`: the first depends on `L`
only and is `O(1/log L)`, the second on `ℓ = log X` only and is `O(1/log ℓ)`
(`eventually_ladderHPart_le`, `eventually_ladderXPart_le`).  Frequencies `W < e` are covered by
monotonicity in `W`.
-/

open Finset MeasureTheory Set Filter Topology RHTower.Sieve

namespace GaloisForLFunctions.MatomakiRadziwill

noncomputable section
set_option autoImplicit false

/-- The part of the ladder bound depending on `L = log h` only. -/
def ladderHPart (L : ℝ) : ℝ :=
  2 * (216 * (1 / (Real.log L / 4) + 2 / (Real.log L / 2)))
    + 2 * (2 * (256 * (52 / seqA L 0)) + 2 * (L ^ 52 * (10 * Real.pi * Real.exp (-(6 / 25) * L)
        + 40 * Real.exp 1 * Real.exp 1 * Real.exp (-96 * Real.log L)))
      + 2 * (2 * Real.exp (-(L / 2))))

/-- The part of the ladder bound depending on `X` only (top pointwise bound `ρ = (log X)^{-3}`). -/
def ladderXPart (X : ℝ) : ℝ :=
  2 * (216 * (1 / (3 / 100 * Real.log (Real.log X) - mertensScaleConst)))
    + 2 * (2 * (256 * (10 / Real.log X + 16 * Real.exp (-ladderTopLow X)))
      + 2 * ((Real.log X ^ 2 + 2) ^ 2 * (1 / Real.log X ^ (3 : ℝ)) ^ 2
        * (6 + 4 * 60000 * 144 * 2 ^ 26 * Real.log X ^ 27
          * Real.exp (-(Real.log X / 50) + 2 * ladderTopHigh X)
          + 384 * (Real.log X + 3))))

/-- `x^n e^{-cx} → 0`. -/
theorem tendsto_pow_mul_exp_neg_mul (n : ℕ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun x : ℝ => x ^ n * Real.exp (-c * x)) atTop (𝓝 0) := by
  have h := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n).comp
    (tendsto_id.const_mul_atTop hc)).const_mul ((c ^ n)⁻¹)
  rw [mul_zero] at h
  refine h.congr fun x => ?_
  simp only [Function.comp, id]
  rw [mul_pow, neg_mul]
  field_simp

/-- **The `L`-part of the ladder bound is small.** -/
theorem eventually_ladderHPart_le {ε : ℝ} (hε : 0 < ε) : ∀ᶠ L : ℝ in atTop, ladderHPart L ≤ ε := by
  have tA : Tendsto (fun L : ℝ => 1 / (Real.log L / 4)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.atTop_div_const (by norm_num))
  have tB : Tendsto (fun L : ℝ => 2 / (Real.log L / 2)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.atTop_div_const (by norm_num))
  have hA0 : Tendsto (fun L : ℝ => seqA L 0) atTop atTop :=
    Real.tendsto_log_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 200)
  have tC : Tendsto (fun L : ℝ => 52 / seqA L 0) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hA0
  have tD1 : Tendsto (fun L : ℝ => L ^ 52 * Real.exp (-(6 / 25) * L)) atTop (𝓝 0) :=
    tendsto_pow_mul_exp_neg_mul 52 (by norm_num)
  have tD2 : Tendsto (fun L : ℝ => L ^ 52 * Real.exp (-96 * Real.log L)) atTop (𝓝 0) := by
    have h := (tendsto_pow_atTop (by norm_num : (44 : ℕ) ≠ 0)).inv_tendsto_atTop (l := atTop)
      (f := fun L : ℝ => L ^ 44)
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
    have e : Real.exp (-96 * Real.log L) = (L ^ 96)⁻¹ := by
      rw [neg_mul, Real.exp_neg,
        show (96 : ℝ) * Real.log L = ((96 : ℕ) : ℝ) * Real.log L by norm_num,
        Real.exp_nat_mul, Real.exp_log hL]
    show (L ^ 44)⁻¹ = L ^ 52 * Real.exp (-96 * Real.log L)
    rw [e]
    field_simp
  have tD : Tendsto (fun L : ℝ => L ^ 52 * (10 * Real.pi * Real.exp (-(6 / 25) * L)
      + 40 * Real.exp 1 * Real.exp 1 * Real.exp (-96 * Real.log L))) atTop (𝓝 0) := by
    have h := (tD1.const_mul (10 * Real.pi)).add (tD2.const_mul (40 * Real.exp 1 * Real.exp 1))
    simp only [mul_zero, add_zero] at h
    exact h.congr fun L => by ring
  have tE : Tendsto (fun L : ℝ => Real.exp (-(L / 2))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.atTop_div_const (by norm_num))
  have h := (((tA.add tB).const_mul 216).const_mul 2).add
    (((((tC.const_mul 256).const_mul 2).add (tD.const_mul 2)).add
      ((tE.const_mul 2).const_mul 2)).const_mul 2)
  simp only [mul_zero, add_zero] at h
  exact h.eventually (ge_mem_nhds hε)

/-- The exceptional term against a majorant: `(u² + 2)² u^{-6} B ≤ 6168/u + 4K u^{25} E'`. -/
theorem exc_majorant {u K E E' : ℝ} (hu : 2 ≤ u) (hK : 0 ≤ K) (hE : 0 ≤ E) (hEE : E ≤ E') :
    (u ^ 2 + 2) ^ 2 * (1 / u ^ (3 : ℝ)) ^ 2 * (6 + K * u ^ 27 * E + 384 * (u + 3))
      ≤ 6168 / u + 4 * K * (u ^ 25 * E') := by
  have hu0 : 0 < u := by linarith
  have h3 : u ^ (3 : ℝ) = u ^ 3 := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [h3]
  have h1 : (u ^ 2 + 2) ^ 2 ≤ 4 * u ^ 4 := by
    have hu2 : 0 ≤ u ^ 2 - 2 := by nlinarith
    nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ 3 * u ^ 2 + 2) hu2]
  have hKE : 0 ≤ K * u ^ 27 * E := mul_nonneg (mul_nonneg hK (pow_nonneg hu0.le 27)) hE
  have hB0 : 0 ≤ 6 + K * u ^ 27 * E + 384 * (u + 3) := by linarith
  have h2 : (u ^ 2 + 2) ^ 2 * (1 / u ^ 3) ^ 2 * (6 + K * u ^ 27 * E + 384 * (u + 3))
      ≤ 4 * u ^ 4 * (1 / u ^ 3) ^ 2 * (6 + K * u ^ 27 * E + 384 * (u + 3)) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 (sq_nonneg _)) hB0
  have h3' : 4 * u ^ 4 * (1 / u ^ 3) ^ 2 * (6 + K * u ^ 27 * E + 384 * (u + 3))
      = 4 * (6 + 384 * (u + 3)) / u ^ 2 + 4 * K * (u ^ 25 * E) := by
    field_simp; ring
  have h4 : 4 * (6 + 384 * (u + 3)) / u ^ 2 ≤ 6168 / u := by
    rw [div_le_div_iff₀ (by positivity) hu0]; nlinarith
  have h5 : 4 * K * (u ^ 25 * E) ≤ 4 * K * (u ^ 25 * E') :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hEE (pow_nonneg hu0.le 25))
      (by linarith)
  linarith

/-- **The `X`-part of the ladder bound is small.** -/
theorem eventually_ladderXPart_le {ε : ℝ} (hε : 0 < ε) : ∀ᶠ X : ℝ in atTop, ladderXPart X ≤ ε := by
  set K : ℝ := 4 * 60000 * 144 * 2 ^ 26 with hK
  have hK0 : 0 ≤ K := by norm_num [hK]
  -- the majorant tends to zero
  have t1 : Tendsto (fun ℓ : ℝ => 1 / (3 / 100 * Real.log ℓ - mertensScaleConst)) atTop (𝓝 0) := by
    have h : Tendsto (fun ℓ : ℝ => 3 / 100 * Real.log ℓ + -mertensScaleConst) atTop atTop :=
      tendsto_atTop_add_const_right _ _ (Real.tendsto_log_atTop.const_mul_atTop (by norm_num))
    exact tendsto_const_nhds.div_atTop (h.congr fun ℓ => (sub_eq_add_neg _ _).symm)
  have t2 : Tendsto (fun ℓ : ℝ => 10 / ℓ) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  have t3 : Tendsto (fun ℓ : ℝ => Real.exp (-ℓ ^ (93 / 100 : ℝ))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_rpow_atTop (by norm_num))
  have t4 : Tendsto (fun ℓ : ℝ => 6168 / ℓ) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  have t5 : Tendsto (fun ℓ : ℝ => ℓ ^ 25 * Real.exp (-(1 / 100) * ℓ)) atTop (𝓝 0) :=
    tendsto_pow_mul_exp_neg_mul 25 (by norm_num)
  have hg := ((t1.const_mul 216).const_mul 2).add
    (((((t2.add (t3.const_mul 16)).const_mul 256).const_mul 2).add
      ((t4.add (t5.const_mul (4 * K))).const_mul 2)).const_mul 2)
  simp only [mul_zero, add_zero] at hg
  -- the `X`-part is below the majorant
  have hmaj : ∀ᶠ ℓ : ℝ in atTop,
      2 * (216 * (1 / (3 / 100 * Real.log ℓ - mertensScaleConst)))
        + 2 * (2 * (256 * (10 / ℓ + 16 * Real.exp (-ℓ ^ (93 / 100 : ℝ))))
          + 2 * ((ℓ ^ 2 + 2) ^ 2 * (1 / ℓ ^ (3 : ℝ)) ^ 2
            * (6 + K * ℓ ^ 27 * Real.exp (-(ℓ / 50) + 2 * ℓ ^ (96 / 100 : ℝ))
              + 384 * (ℓ + 3))))
      ≤ 2 * (216 * (1 / (3 / 100 * Real.log ℓ - mertensScaleConst)))
        + 2 * (2 * (256 * (10 / ℓ + 16 * Real.exp (-ℓ ^ (93 / 100 : ℝ))))
          + 2 * (6168 / ℓ + 4 * K * (ℓ ^ 25 * Real.exp (-(1 / 100) * ℓ)))) := by
    filter_upwards [eventually_ge_atTop 2,
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 4 / 100)).eventually_ge_atTop 200]
      with ℓ hℓ2 hℓ200
    have hℓ0 : 0 < ℓ := by linarith
    have hEE : Real.exp (-(ℓ / 50) + 2 * ℓ ^ (96 / 100 : ℝ)) ≤ Real.exp (-(1 / 100) * ℓ) := by
      refine Real.exp_le_exp.mpr ?_
      have e : ℓ = ℓ ^ (96 / 100 : ℝ) * ℓ ^ (4 / 100 : ℝ) := by
        rw [← Real.rpow_add hℓ0]; norm_num
      have h96 : 0 ≤ ℓ ^ (96 / 100 : ℝ) := Real.rpow_nonneg hℓ0.le _
      nlinarith [mul_nonneg h96 (sub_nonneg.mpr hℓ200)]
    have := exc_majorant hℓ2 hK0 (Real.exp_pos _).le hEE
    linarith
  have hℓ : ∀ᶠ ℓ : ℝ in atTop,
      2 * (216 * (1 / (3 / 100 * Real.log ℓ - mertensScaleConst)))
        + 2 * (2 * (256 * (10 / ℓ + 16 * Real.exp (-ℓ ^ (93 / 100 : ℝ))))
          + 2 * ((ℓ ^ 2 + 2) ^ 2 * (1 / ℓ ^ (3 : ℝ)) ^ 2
            * (6 + K * ℓ ^ 27 * Real.exp (-(ℓ / 50) + 2 * ℓ ^ (96 / 100 : ℝ))
              + 384 * (ℓ + 3)))) ≤ ε :=
    (hmaj.and (hg.eventually (ge_mem_nhds hε))).mono fun ℓ h => le_trans h.1 h.2
  filter_upwards [Real.tendsto_log_atTop.eventually hℓ] with X hX
  exact hX

/-- `ℓ^a + 1 ≤ ℓ^b` for large `ℓ` when `0 < a < b`. -/
theorem eventually_rpow_add_one_le {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∀ᶠ ℓ : ℝ in atTop, ℓ ^ a + 1 ≤ ℓ ^ b := by
  filter_upwards [(tendsto_rpow_atTop ha).eventually_ge_atTop 1,
    (tendsto_rpow_atTop (sub_pos.mpr hab)).eventually_ge_atTop 2, eventually_gt_atTop 0]
    with ℓ h1 h2 h0
  have e : ℓ ^ b = ℓ ^ a * ℓ ^ (b - a) := by rw [← Real.rpow_add h0]; congr 1; ring
  rw [e]; nlinarith

/-- The conditions on `L = log h`. -/
theorem eventually_ladder_L_conditions (x₀ : ℝ) :
    ∀ᶠ L : ℝ in atTop, 2 ^ 20 ≤ L ∧ x₀ ≤ L / 2 ∧ 0 < Real.log L
      ∧ Real.log L / 4 ≤ Real.log (seqB L 0 / seqA L 0) - mertensScaleConst
      ∧ 2 * mertensScaleConst + 2 * (Real.log L / 2) ≤ Real.log (seqA L 1) := by
  have hy : ∀ᶠ y : ℝ in atTop, 0 < y ∧ Real.log y ≤ y / 4
      ∧ 2 * (Real.log 2 + Real.log 200 + mertensScaleConst) ≤ y
      ∧ 2 * mertensScaleConst + Real.log 2 ≤ y := by
    filter_upwards [eventually_gt_atTop 0,
      Real.isLittleO_log_id_atTop.bound (by norm_num : (0 : ℝ) < 1 / 4),
      eventually_ge_atTop (2 * (Real.log 2 + Real.log 200 + mertensScaleConst)),
      eventually_ge_atTop (2 * mertensScaleConst + Real.log 2)] with y hy0 hlog h1 h2
    refine ⟨hy0, ?_, h1, h2⟩
    rw [Real.norm_eq_abs, Real.norm_eq_abs, id, abs_of_pos hy0] at hlog
    linarith [le_abs_self (Real.log y)]
  filter_upwards [eventually_ge_atTop (2 ^ 20 : ℝ), eventually_ge_atTop (2 * x₀),
    Real.tendsto_log_atTop.eventually hy] with L hL hx hyL
  obtain ⟨hlogL, hll, h1, h2⟩ := hyL
  have hL0 : 0 < L := by linarith
  refine ⟨hL, by linarith, hlogL, ?_, ?_⟩
  · have e : Real.log (seqB L 0 / seqA L 0)
        = Real.log L - Real.log 2 - Real.log 200 - Real.log (Real.log L) := by
      show Real.log ((L / 2) / (200 * Real.log L)) = _
      rw [Real.log_div (div_pos hL0 two_pos).ne' (mul_pos (by norm_num) hlogL).ne',
        Real.log_div hL0.ne' (by norm_num), Real.log_mul (by norm_num) hlogL.ne']
      ring
    rw [e]
    linarith
  · have e : Real.log (seqA L 1) = 2 * Real.log L - Real.log 2 := by
      show Real.log (2 * (L / 2) ^ 2) = _
      rw [Real.log_mul (by norm_num) (pow_pos (div_pos hL0 two_pos) 2).ne', Real.log_pow,
        Real.log_div hL0.ne' (by norm_num)]
      push_cast
      ring
    rw [e]
    linarith

/-- The conditions on `X` for a fixed `L` (with `b = b_1(L)`). -/
theorem eventually_top_conditions (b : ℝ) :
    ∀ᶠ X : ℝ in atTop, Real.exp 1 ≤ X ∧ 2 ≤ Real.log X ∧ 1 ≤ ladderTopLow X
      ∧ ladderTopLow X + 1 ≤ ladderTopHigh X
      ∧ 0 < 3 / 100 * Real.log (Real.log X) - mertensScaleConst
      ∧ 864 * Real.log X
          ≤ (Real.log X ^ (93 / 100 : ℝ) / 4) ^ (1 / 8 : ℝ) * Real.log X ^ (93 / 100 : ℝ)
      ∧ b ≤ ladderTopLow X ∧ Real.log X ^ (9 / 10 : ℝ) ≤ ladderTopLow X - 1 := by
  have hℓ : ∀ᶠ ℓ : ℝ in atTop, 2 ≤ ℓ ∧ 1 ≤ ℓ ^ (93 / 100 : ℝ)
      ∧ ℓ ^ (93 / 100 : ℝ) + 1 ≤ ℓ ^ (96 / 100 : ℝ)
      ∧ 0 < 3 / 100 * Real.log ℓ - mertensScaleConst
      ∧ 864 * ℓ ≤ (ℓ ^ (93 / 100 : ℝ) / 4) ^ (1 / 8 : ℝ) * ℓ ^ (93 / 100 : ℝ)
      ∧ b ≤ ℓ ^ (93 / 100 : ℝ) ∧ ℓ ^ (9 / 10 : ℝ) + 1 ≤ ℓ ^ (93 / 100 : ℝ) := by
    filter_upwards [eventually_ge_atTop 2,
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 93 / 100)).eventually_ge_atTop (max b 1),
      eventually_rpow_add_one_le (by norm_num : (0 : ℝ) < 93 / 100)
        (by norm_num : (93 / 100 : ℝ) < 96 / 100),
      Real.tendsto_log_atTop.eventually_gt_atTop (100 / 3 * mertensScaleConst),
      eventually_last_scale_large,
      eventually_rpow_add_one_le (by norm_num : (0 : ℝ) < 9 / 10)
        (by norm_num : (9 / 10 : ℝ) < 93 / 100)]
      with ℓ h2 hb h96 hlog hl h90
    exact ⟨h2, le_trans (le_max_right _ _) hb, h96, by linarith, hl,
      le_trans (le_max_left _ _) hb, h90⟩
  filter_upwards [Real.tendsto_log_atTop.eventually hℓ, eventually_ge_atTop (Real.exp 1)]
    with X h hXe
  obtain ⟨h2, h1, h96, hlog, hl, hb, h90⟩ := h
  exact ⟨hXe, h2, h1, h96, hlog, hl, hb, by unfold ladderTopLow; linarith⟩

/-- **Matomäki–Radziwiłł in mean square for `λχ`, `χ` non-principal.** -/
theorem exists_mean_square_twLiouville_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L → ∃ X₀ : ℝ, ∀ X : ℕ, X₀ ≤ (X : ℝ) → ∀ W : ℝ, 0 ≤ W →
      W ≤ X * Real.exp (-(L / 2)) →
        (∫ w in Icc (-W) W, ‖fullPoly (twLiouville χ) X w‖ ^ 2) ≤ ε := by
  obtain ⟨x₀, -, hx₀⟩ := exists_poly_exp_le (144 * Real.exp 1 * 2 ^ 48) 66
  have hε2 : 0 < ε / 2 := by linarith
  obtain ⟨L₀, hL₀⟩ := eventually_atTop.mp
    ((eventually_ladderHPart_le hε2).and (eventually_ladder_L_conditions x₀))
  refine ⟨L₀, fun L hLL => ?_⟩
  obtain ⟨hHP, hL, hx₀L, hlogL, h0, h1⟩ := hL₀ L hLL
  obtain ⟨X₁, hX₁⟩ := exists_norm_blockQ_twLiouville_le χ hχ (θ := 9 / 10) (A := 3)
    (by norm_num) (by norm_num)
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp
    ((eventually_ladderXPart_le hε2).and ((eventually_top_conditions (seqB L 1)).and
      ((eventually_ge_atTop X₁).and (eventually_ge_atTop (Real.exp 1 * Real.exp (L / 2))))))
  refine ⟨X₀, fun X hX W hW0 hWX => ?_⟩
  obtain ⟨hXP, ⟨hXe, hlog2, htop1, htop2, htop3, hlarge, hJb, hθ⟩, hXX₁, hXL⟩ := hX₀ X hX
  set f := twLiouville χ with hfdef
  have hf : ∀ n, ‖f n‖ ≤ 1 := norm_twLiouville_le χ
  have hmul : ∀ a b, f (a * b) = f a * f b := twLiouville_mul χ
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 1) hXe
  have hJ : 2 ≤ ladderJ hL (X : ℝ) := ladderJ_pos hL hJb
  have hstep : ∀ x : ℝ, L / 2 ≤ x →
      144 * Real.exp 1 * 2 ^ 48 * x ^ 66 * Real.exp (-(152 / 100) * x) ≤ Real.exp (-x) :=
    fun x hx => hx₀ x (le_trans hx₀L hx)
  -- enlarge the frequency range to `W' = max(W, e)`
  set W' := max W (Real.exp 1) with hW'def
  have hW'e : Real.exp 1 ≤ W' := le_max_right _ _
  have hWW' : W ≤ W' := le_max_left _ _
  have heX : Real.exp 1 ≤ X * Real.exp (-(L / 2)) := by
    rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _)]; exact hXL
  have hW'X : W' ≤ X * Real.exp (-(L / 2)) := max_le hWX heX
  have hexpL : Real.exp (-(L / 2)) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
  have hW'X' : W' ≤ X := le_trans hW'X (by nlinarith)
  have hW'1 : 1 ≤ W' := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hW'e
  -- Route T on the top scale
  have hρ : ∀ v ∈ (ladderConfig hL (X : ℝ)).topBlocks (Real.log X), ∀ w ∈ Icc (-W') W',
      ‖blockQ f (ladderConfig hL (X : ℝ)).top (Real.log X) v w‖ ≤ 1 / Real.log X ^ (3 : ℝ) := by
    intro v _ w hw
    have hlogPa : Real.log X ^ (9 / 10 : ℝ)
        ≤ Real.log (⌊Real.exp (ladderTopLow (X : ℝ))⌋₊ : ℝ) :=
      le_trans hθ (log_floor_exp_ge htop1)
    have hPb : ((⌊Real.exp (ladderTopHigh (X : ℝ))⌋₊ : ℕ) : ℝ) ≤ X := by
      obtain ⟨-, hhX⟩ := ladderTop_le (one_le_log_of_exp_le hXe)
      calc ((⌊Real.exp (ladderTopHigh (X : ℝ))⌋₊ : ℕ) : ℝ) ≤ Real.exp (ladderTopHigh X) :=
            Nat.floor_le (Real.exp_pos _).le
        _ ≤ Real.exp (Real.log X) := Real.exp_le_exp.mpr hhX
        _ = X := Real.exp_log hX0
    have hw' : 2 * Real.pi * |w| ≤ X := by
      have h1 : |w| ≤ W' := abs_le.mpr ⟨by linarith [hw.1], hw.2⟩
      have h2π : 2 * Real.pi * Real.exp (-(L / 2)) ≤ 1 := by
        rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos _)]
        linarith [Real.add_one_le_exp (L / 2), Real.pi_lt_d2]
      have hpi := Real.pi_pos
      calc 2 * Real.pi * |w| ≤ 2 * Real.pi * (X * Real.exp (-(L / 2))) :=
            mul_le_mul_of_nonneg_left (le_trans h1 hW'X) (by positivity)
        _ = X * (2 * Real.pi * Real.exp (-(L / 2))) := by ring
        _ ≤ X * 1 := mul_le_mul_of_nonneg_left h2π hX0.le
        _ = X := mul_one _
    exact hX₁ X hXX₁ _ _ (Real.log X) hlog2 hlogPa hPb v w hw'
  -- the two parts of the ladder bound
  have hrough := ladder_rough_le hf hmul hL hstep hXe hJ hlarge hW'e hW'X measurableSet_Icc
    subset_rfl hρ
  have hnon := ladder_nonrough_le hf hL hlogL h0 h1 hXe htop1 htop2 htop3 hW'1 hW'X'
  -- `|F|² ≤ 2|F − F_S|² + 2|F_S|²`, integrated over `[−W', W']`
  set R := logPoly (coefA f) ((ladderConfig hL (X : ℝ)).ladderS X) with hRdef
  have hcF : Continuous (fullPoly f X) := continuous_logPoly _ _
  have hcR : Continuous R := continuous_logPoly _ _
  have hi0 : IntegrableOn (fun w => ‖fullPoly f X w‖ ^ 2) (Icc (-W') W') :=
    (hcF.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hi1 : IntegrableOn (fun w => ‖fullPoly f X w - R w‖ ^ 2) (Icc (-W') W') :=
    ((hcF.sub hcR).norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hi2 : IntegrableOn (fun w => ‖R w‖ ^ 2) (Icc (-W') W') :=
    (hcR.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hsplit : (∫ w in Icc (-W') W', ‖fullPoly f X w‖ ^ 2)
      ≤ 2 * (∫ w in Icc (-W') W', ‖fullPoly f X w - R w‖ ^ 2)
        + 2 * (∫ w in Icc (-W') W', ‖R w‖ ^ 2) := by
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add (hi1.const_mul 2) (hi2.const_mul 2)]
    exact setIntegral_mono hi0 ((hi1.const_mul 2).add (hi2.const_mul 2))
      fun w => normSq_le_two_mul_add _ _
  have hmono : (∫ w in Icc (-W) W, ‖fullPoly f X w‖ ^ 2)
      ≤ ∫ w in Icc (-W') W', ‖fullPoly f X w‖ ^ 2 :=
    setIntegral_mono_set hi0 (ae_of_all _ fun w => sq_nonneg _)
      (Icc_subset_Icc (by linarith) hWW').eventuallyLE
  have hHP' := hHP
  have hXP' := hXP
  unfold ladderHPart at hHP'
  unfold ladderXPart at hXP'
  linarith

end

end GaloisForLFunctions.MatomakiRadziwill
