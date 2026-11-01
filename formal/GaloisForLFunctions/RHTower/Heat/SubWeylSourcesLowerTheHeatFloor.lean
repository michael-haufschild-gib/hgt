import GaloisForLFunctions.RHTower.Heat.FourSubWeylCauchyBounds

/-! # Sub-Weyl source bounds lower the heat coefficient below `2/3`

All four Gaussian profile rates exceed the Euler-window loss at `133/200`.
The positive window dominates every derivative of order at most `log t`;
existing coefficient positivity and heat propagation give every even order
and every larger heat, uniformly at sufficiently large absolute height.
-/

noncomputable section
open Complex MeasureTheory Filter Topology Metric
open scoped ComplexOrder
open GaloisForLFunctions.HTGeometry

namespace RHTower

private def subWeylRateOne (κ : ℝ) : ℝ := 31 / 200 + (3 / 100) / 2 - (3 / 100) ^ 2 * κ / 2
private def subWeylRateTwo (κ : ℝ) : ℝ := 1 / 13 + (3 / 13) / 2 - (3 / 13) ^ 2 * κ / 2
private def subWeylRateThree (κ : ℝ) : ℝ := 1 / 53 + (23 / 53) / 2 - (23 / 53) ^ 2 * κ / 2
private def subWeylRateFour (η κ : ℝ) : ℝ := η + subWeylGain η / 2 - subWeylGain η ^ 2 * κ / 2

private theorem subWeyl_gaussian_profile {u s κ β c b w n : ℝ}
    (hu : 0 ≤ u) (hs : 0 ≤ s) (hus : u ^ 2 * s ^ 2 = κ * u)
    (hb : b ≤ β + c / 2 - c ^ 2 * κ / 2) :
    -(w ^ 2 / 2) + (n - β * u - c * u * (1 / 2 - |s * w|)) ≤ n - b * u := by
  have h1 := sq_nonneg (|w| - c * u * s)
  have h2 := sq_abs w
  have key : -(w ^ 2 / 2) + c * u * s * |w| ≤ c ^ 2 * κ * u / 2 := by
    have hscale := congrArg (fun v : ℝ => c ^ 2 * v) hus
    nlinarith only [h1, h2, hscale]
  have hbu := mul_le_mul_of_nonneg_right hb hu
  rw [abs_mul, abs_of_nonneg hs]
  nlinarith only [key, hbu]

private theorem exists_xiSliceHeatTransfer_pos_low_order_subWeyl {κ η ω : ℝ} (hκ : 3 / 5 ≤ κ)
    (hκ1 : κ ≤ 1) (hη : 0 < η) (hη1 : η ≤ 1 / 20) (hω : 0 < ω) (hω1 : ω ≤ 1 / 100)
    (hgap₁ : 0 < (κ / 2 - 1 / 2 - 2 * η - 5 / 6 * ω ^ 2) + subWeylRateOne κ)
    (hgap₂ : 0 < (κ / 2 - 1 / 2 - 2 * η - 5 / 6 * ω ^ 2) + subWeylRateTwo κ)
    (hgap₃ : 0 < (κ / 2 - 1 / 2 - 2 * η - 5 / 6 * ω ^ 2) + subWeylRateThree κ)
    (hgap₄ : 0 < (κ / 2 - 1 / 2 - 2 * η - 5 / 6 * ω ^ 2) + subWeylRateFour η κ) :
    ∃ t₀ : ℝ, 80 ≤ t₀ ∧ ∀ t : ℝ, t₀ ≤ t → ∀ m : ℕ, 1 ≤ m → (2 * m : ℝ) ≤ Real.log t →
      0 < DeBruijn.xiSliceHeatTransfer (κ / Real.log t) 0 t (2 * m) := by
  obtain ⟨C, hC, hinner⟩ := exists_norm_iteratedDeriv_xiSliceProduct_le_inner_four_subWeyl_profiles hη hη1
  obtain ⟨t₄, -, hM4⟩ := exists_iteratedDeriv_xiSliceProduct_ge_euler_from (η := 1 / 20)
    (by norm_num) (by norm_num)
  obtain ⟨E, hEdef⟩ : ∃ E, E = xiEulerConstant η := ⟨_, rfl⟩
  obtain ⟨E₈, hE₈def⟩ : ∃ E₈, E₈ = xiEulerConstant (1 / 20) := ⟨_, rfl⟩
  have hE0 : 0 < E := hEdef ▸ xiEulerConstant_pos hη
  have hE₈0 : 0 < E₈ := hE₈def ▸ xiEulerConstant_pos (by norm_num)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hκ0 : 0 < κ := by linarith only [hκ]
  obtain ⟨c, hcdef⟩ : ∃ c, c = subWeylGain η := ⟨_, rfl⟩
  obtain ⟨a, hadef⟩ : ∃ a : ℝ, a = κ / 2 - 1 / 2 - 2 * η - 5 / 6 * ω ^ 2 := ⟨_, rfl⟩
  obtain ⟨b, hbdef⟩ : ∃ b : ℝ,
      b = min (min (subWeylRateOne κ) (subWeylRateTwo κ))
        (min (subWeylRateThree κ) (subWeylRateFour η κ)) := ⟨_, rfl⟩
  have hb₁ : b ≤ 31 / 200 + (3 / 100) / 2 - (3 / 100) ^ 2 * κ / 2 := by
    rw [hbdef]
    exact (min_le_left _ _).trans (min_le_left _ _)
  have hb₂ : b ≤ 1 / 13 + (3 / 13) / 2 - (3 / 13) ^ 2 * κ / 2 := by
    rw [hbdef]
    exact (min_le_left _ _).trans (min_le_right _ _)
  have hb₃ : b ≤ 1 / 53 + (23 / 53) / 2 - (23 / 53) ^ 2 * κ / 2 := by
    rw [hbdef]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hb₄ : b ≤ η + c / 2 - c ^ 2 * κ / 2 := by
    rw [hbdef, hcdef]
    exact (min_le_right _ _).trans (min_le_right _ _)
  have hgap : 0 < a + b := by
    rw [hadef, hbdef]
    rcases min_choice (min (subWeylRateOne κ) (subWeylRateTwo κ))
      (min (subWeylRateThree κ) (subWeylRateFour η κ)) with h | h <;> rw [h]
    · rcases min_choice (subWeylRateOne κ) (subWeylRateTwo κ) with h' | h' <;> rw [h']
      · exact hgap₁
      · exact hgap₂
    · rcases min_choice (subWeylRateThree κ) (subWeylRateFour η κ) with h' | h' <;> rw [h']
      · exact hgap₃
      · exact hgap₄
  obtain ⟨K, hKdef⟩ : ∃ K, K = 80 * Real.pi * Real.sqrt 2 * (4 * C)
      * Real.exp (2 * (2 * E + Real.log 2 + 2 * E₈) + (2 * (Real.log 2 + 2 * E) + 1)) / ω :=
    ⟨_, rfl⟩
  have hK0 : 0 < K := by rw [hKdef]; positivity
  have e5 := (tendsto_order.1 (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (a + b)
    hgap)).2 (1 / K) (by positivity)
  obtain ⟨U, hU⟩ := Filter.eventually_atTop.mp e5
  obtain ⟨L₀, hL₀⟩ : ∃ L₀, L₀ = max (max (Real.log 80) (Real.log t₄))
      (max (2 * (Real.log 2 + 2 * E₈)) (max U 1)) := ⟨_, rfl⟩
  refine ⟨max 80 (max t₄ (Real.exp L₀)), le_max_left _ _, ?_⟩
  intro t ht m hm1 hmu
  have ht80 : 80 ≤ t := le_trans (le_max_left _ _) ht
  have ht4 : t₄ ≤ t := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) ht
  have htL : Real.exp L₀ ≤ t := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) ht
  have ht0 : 0 < t := by linarith only [ht80]
  obtain ⟨u, hudef⟩ : ∃ u, u = Real.log t := ⟨_, rfl⟩
  have hLu : L₀ ≤ u := by
    rw [hudef, ← Real.log_exp L₀]; exact Real.log_le_log (Real.exp_pos _) htL
  rw [hL₀] at hLu
  have hu2 : 2 * (Real.log 2 + 2 * E₈) ≤ u :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hLu
  have huU : U ≤ u :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hLu
  have hu1 : 1 ≤ u :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hLu
  have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu1
  have hKu : u * K < Real.exp ((a + b) * u) := by
    have h := hU u huU
    rw [Real.rpow_one, show -(a + b) * u = -((a + b) * u) by ring, Real.exp_neg] at h
    have hx := Real.exp_pos ((a + b) * u)
    rw [lt_div_iff₀ hK0] at h
    calc u * K = u * (Real.exp ((a + b) * u))⁻¹ * K * Real.exp ((a + b) * u) := by field_simp
      _ < 1 * Real.exp ((a + b) * u) := mul_lt_mul_of_pos_right h hx
      _ = Real.exp ((a + b) * u) := one_mul _
  -- the order and the heat
  obtain ⟨N, hNdef⟩ : ∃ N, N = 2 * m := ⟨_, rfl⟩
  have hN1 : 1 ≤ N := by omega
  have hNu : (N : ℝ) ≤ u := by rw [hNdef, hudef]; push_cast; exact hmu
  rw [← hudef]
  obtain ⟨lam, hlamdef⟩ : ∃ lam, lam = κ / u := ⟨_, rfl⟩
  rw [← hlamdef, ← hNdef]
  have hlam0 : 0 < lam := by rw [hlamdef]; positivity
  obtain ⟨s, hsdef⟩ : ∃ s, s = Real.sqrt lam := ⟨_, rfl⟩
  have hs0 : 0 < s := by rw [hsdef]; exact Real.sqrt_pos.mpr hlam0
  have hs2 : s ^ 2 = lam := by rw [hsdef]; exact Real.sq_sqrt hlam0.le
  -- the representation and its real part
  have hrep := DeBruijn.xiSliceHeatTransfer_eq_integral_iteratedDeriv hlam0.le t N
  have hint := DeBruijn.integrable_gauss_mul_iteratedDeriv_xiSliceProduct hlam0.le t N
  rw [← hsdef] at hrep hint
  set F : ℝ → ℂ := fun w => ((Real.exp (-(w ^ 2 / 2)) : ℝ) : ℂ)
    * (iteratedDeriv N (xiSliceProduct t) ((s * w : ℝ) : ℂ) / N.factorial) with hF
  have hre : ∫ w, (F w).re = (((Real.sqrt (2 * Real.pi) : ℝ) : ℂ)
      * DeBruijn.xiSliceHeatTransfer lam 0 t N).re := by
    have := integral_re hint
    simp only [RCLike.re_to_complex] at this
    rw [hrep]; exact this
  have hfact0 : (0 : ℝ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
  have hFre : ∀ w, (F w).re = Real.exp (-(w ^ 2 / 2))
      * ((iteratedDeriv N (xiSliceProduct t) ((s * w : ℝ) : ℂ)).re / N.factorial) := by
    intro w
    simp only [hF]
    rw [Complex.re_ofReal_mul, Complex.div_natCast_re]
  -- constants of the window argument
  obtain ⟨S₀, hS₀⟩ : ∃ S₀, S₀ = xiSliceReal t (1 / 2 + 2 * η) := ⟨_, rfl⟩
  have hS₀0 : 0 < S₀ := by rw [hS₀]; exact xiSliceReal_pos t (by linarith only [hη])
  have hlogt2 : Real.log (t / 2) = u - Real.log 2 := by
    rw [Real.log_div ht0.ne' (by norm_num), hudef]
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = (u - Real.log 2 - 2 * E₈) ^ N / N.factorial
      * (1 / (40 * Real.pi * Real.sqrt (2 * u))) := ⟨_, rfl⟩
  have hL'0 : 0 < u - Real.log 2 - 2 * E₈ := by linarith only [hu2, hl2, hE₈0]
  have hQ0 : 0 ≤ Q := by
    rw [hQ]; exact mul_nonneg (div_nonneg (pow_pos hL'0 N).le hfact0.le) (by positivity)
  obtain ⟨P₀, hP₀⟩ : ∃ P₀, P₀ = S₀ * Real.exp (u * a - 2 * (Real.log 2 + 2 * E)) * Q := ⟨_, rfl⟩
  obtain ⟨B₀, hB₀⟩ : ∃ B₀, B₀ = 4 * C * S₀ * (Real.exp (N - b * u)
      * ((u + 2 * E) / N) ^ N) := ⟨_, rfl⟩
  have hwin := DeBruijn.integral_ge_of_window (h := fun w => (F w).re) hint.re
    (a := κ / s) (b := (κ + ω) / s) (c := 1 / 2 / s) (P := P₀) (B := B₀)
    (div_le_div_of_nonneg_right (by linarith only [hω]) hs0.le) (by positivity)
    (div_le_div_of_nonneg_right (by linarith only [hκ]) hs0.le) ?_ ?_ ?_
  rotate_left
  · -- the window
    intro w hw
    have hx1 : κ ≤ s * w := by
      have := (div_le_iff₀ hs0).mp hw.1
      simpa only [mul_comm] using this
    have hx2 : s * w ≤ κ + ω := by
      have := (le_div_iff₀ hs0).mp hw.2
      simpa only [mul_comm] using this
    have hM := hM4 t ht4 (s * w) (by linarith only [hx1, hκ])
      (by linarith only [hx2, hκ1, hω1]) N hN1 (by rw [← hudef]; exact hNu)
    rw [← div_eq_inv_mul, Complex.div_natCast_re, hlogt2, ← hE₈def, ← hudef] at hM
    have hF' := xiSliceReal_mul_gauss_ge_window_width (t := t) hη
      (by linarith only [hη1, hκ]) hκ hκ1 (by linarith only [hω1])
      (by linarith only [ht80]) hx1 hx2 (by linarith only [hx2, hκ1, hω1, ht80])
    rw [← hudef, ← hEdef, ← hS₀,
      show u * (κ / 2 - 1 / 2 - 2 * η - 5 / 6 * ω ^ 2) = u * a by rw [hadef]] at hF'
    have hg : Real.exp (-(w ^ 2 / 2)) = Real.exp (-((s * w) ^ 2 * u / (2 * κ))) := by
      congr 2
      rw [mul_pow, hs2, hlamdef]
      field_simp
    rw [hFre, hg, hP₀]
    calc S₀ * Real.exp (u * a - 2 * (Real.log 2 + 2 * E)) * Q
        ≤ xiSliceReal t (s * w) * Real.exp (-((s * w) ^ 2 * u / (2 * κ))) * Q :=
          mul_le_mul_of_nonneg_right hF' hQ0
      _ = Real.exp (-((s * w) ^ 2 * u / (2 * κ)))
          * (xiSliceReal t (s * w) * (u - Real.log 2 - 2 * E₈) ^ N / N.factorial
            * (1 / (40 * Real.pi * Real.sqrt (2 * u)))) := by rw [hQ]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hM (Real.exp_pos _).le
  · -- the inner region
    intro w hw
    have hx : |s * w| < 1 / 2 := by
      rw [abs_mul, abs_of_pos hs0, ← lt_div_iff₀' hs0]
      exact abs_lt.mpr ⟨hw.1, hw.2⟩
    have hb := hinner t ht80 (s * w) hx N hN1 (by rw [← hudef]; exact hNu)
    rw [← hudef, ← hEdef, ← hS₀, ← hcdef] at hb
    rw [hFre]
    have hg0 := Real.exp_pos (-(w ^ 2 / 2))
    have hsw : |s * w| = s * |w| := by rw [abs_mul, abs_of_pos hs0]
    have hus : u ^ 2 * s ^ 2 = κ * u := by
      rw [hs2, hlamdef]; field_simp
    have h2 : |w| ^ 2 = w ^ 2 := sq_abs w
    have hsq₁ : -(w ^ 2 / 2) + (N - 31 / 200 * u - 3 / 100 * u * (1 / 2 - |s * w|)) ≤ N - b * u :=
      subWeyl_gaussian_profile hu0.le hs0.le hus hb₁
    have hsq₂ : -(w ^ 2 / 2) + (N - u / 13 - 3 / 13 * u * (1 / 2 - |s * w|)) ≤ N - b * u := by
      have h := subWeyl_gaussian_profile (w := w) (n := (N : ℝ)) hu0.le hs0.le hus hb₂
      rw [show (1 / 13 : ℝ) * u = u / 13 by ring] at h
      exact h
    have hsq₃ : -(w ^ 2 / 2) + (N - u / 53 - 23 / 53 * u * (1 / 2 - |s * w|)) ≤ N - b * u := by
      have h := subWeyl_gaussian_profile (w := w) (n := (N : ℝ)) hu0.le hs0.le hus hb₃
      rw [show (1 / 53 : ℝ) * u = u / 53 by ring] at h
      exact h
    have hsq₄ : -(w ^ 2 / 2) + (N - η * u - c * u * (1 / 2 - |s * w|)) ≤ N - b * u :=
      subWeyl_gaussian_profile hu0.le hs0.le hus hb₄
    have hre1 : |(iteratedDeriv N (xiSliceProduct t) ((s * w : ℝ) : ℂ)).re| / N.factorial
        ≤ C * S₀ * ((Real.exp (N - 31 / 200 * u - 3 / 100 * u * (1 / 2 - |s * w|))
          + Real.exp (N - u / 13 - 3 / 13 * u * (1 / 2 - |s * w|))
          + Real.exp (N - u / 53 - 23 / 53 * u * (1 / 2 - |s * w|))
          + Real.exp (N - η * u - c * u * (1 / 2 - |s * w|))) * ((u + 2 * E) / N) ^ N) :=
      le_trans (div_le_div_of_nonneg_right (Complex.abs_re_le_norm _) hfact0.le) hb
    have hX0 : 0 ≤ ((u + 2 * E) / N) ^ N := by positivity
    have habs : |Real.exp (-(w ^ 2 / 2))
        * ((iteratedDeriv N (xiSliceProduct t) ((s * w : ℝ) : ℂ)).re / N.factorial)| ≤ B₀ := by
      rw [abs_mul, abs_of_pos hg0, abs_div, abs_of_pos hfact0]
      calc Real.exp (-(w ^ 2 / 2)) * (|(iteratedDeriv N (xiSliceProduct t)
            ((s * w : ℝ) : ℂ)).re| / N.factorial)
          ≤ Real.exp (-(w ^ 2 / 2)) * (C * S₀ * ((Real.exp (N - 31 / 200 * u - 3 / 100 * u * (1 / 2 - |s * w|))
            + Real.exp (N - u / 13 - 3 / 13 * u * (1 / 2 - |s * w|))
            + Real.exp (N - u / 53 - 23 / 53 * u * (1 / 2 - |s * w|))
          + Real.exp (N - η * u - c * u * (1 / 2 - |s * w|))) * ((u + 2 * E) / N) ^ N)) :=
            mul_le_mul_of_nonneg_left hre1 hg0.le
        _ = C * S₀ * ((Real.exp (-(w ^ 2 / 2) + (N - 31 / 200 * u - 3 / 100 * u * (1 / 2 - |s * w|)))
            + Real.exp (-(w ^ 2 / 2) + (N - u / 13 - 3 / 13 * u * (1 / 2 - |s * w|)))
            + Real.exp (-(w ^ 2 / 2) + (N - u / 53 - 23 / 53 * u * (1 / 2 - |s * w|)))
            + Real.exp (-(w ^ 2 / 2) + (N - η * u - c * u * (1 / 2 - |s * w|))))
            * ((u + 2 * E) / N) ^ N) := by
            rw [Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_add]; ring
        _ ≤ C * S₀ * ((Real.exp (N - b * u) + Real.exp (N - b * u) + Real.exp (N - b * u) + Real.exp (N - b * u))
            * ((u + 2 * E) / N) ^ N) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
              (add_le_add (add_le_add (add_le_add (Real.exp_le_exp.mpr hsq₁)
                (Real.exp_le_exp.mpr hsq₂)) (Real.exp_le_exp.mpr hsq₃)) (Real.exp_le_exp.mpr hsq₄)) hX0)
              (mul_nonneg hC.le hS₀0.le)
        _ = B₀ := by rw [hB₀]; ring
    exact (neg_le_neg habs).trans (neg_abs_le _)
  · -- outside the inner region
    intro w hw
    have hx : 1 / 2 ≤ |s * w| := by
      rw [abs_mul, abs_of_pos hs0, ← div_le_iff₀' hs0]
      by_contra hcon
      push Not at hcon
      exact hw (abs_lt.mp hcon)
    rw [hFre]
    have h0 := DeBruijn.re_iteratedDeriv_xiSliceProduct_even_nonneg t m hx
    rw [← hNdef] at h0
    exact mul_nonneg (Real.exp_pos _).le (div_nonneg h0 hfact0.le)
  -- the comparison
  have hcmp := heat_window_comparison_gen (a := a) (b := b) (w := ω) (C := 4 * C)
    hω (by positivity) hE0.le hE₈0.le hu0 hu2 (by rw [← hKdef]; exact hKu) hN1 hNu
  have hpos : 0 < ((κ + ω) / s - κ / s) * P₀ - 2 * (1 / 2 / s) * B₀ := by
    have e : ((κ + ω) / s - κ / s) * P₀ - 2 * (1 / 2 / s) * B₀
        = (ω * P₀ - B₀) / s := by field_simp; ring
    rw [e]
    refine div_pos ?_ hs0
    rw [hP₀, hB₀]
    rw [← hQ] at hcmp
    have h := mul_lt_mul_of_pos_left hcmp hS₀0
    rw [sub_pos]
    calc 4 * C * S₀ * (Real.exp (N - b * u) * ((u + 2 * E) / N) ^ N)
        < 2 * (4 * C * S₀ * (Real.exp (N - b * u) * ((u + 2 * E) / N) ^ N)) := by
          have : 0 < 4 * C * S₀ * (Real.exp (N - b * u) * ((u + 2 * E) / N) ^ N) := by positivity
          linarith only [this]
      _ = S₀ * (2 * (4 * C * (Real.exp (N - b * u) * ((u + 2 * E) / N) ^ N))) := by ring
      _ < S₀ * (ω * (Real.exp (u * a - 2 * (Real.log 2 + 2 * E)) * Q)) := h
      _ = ω * (S₀ * Real.exp (u * a - 2 * (Real.log 2 + 2 * E)) * Q) := by ring
  have hT := lt_of_lt_of_le hpos (le_of_le_of_eq hwin hre)
  rw [Complex.re_ofReal_mul] at hT
  have hsq : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hTre : 0 < (DeBruijn.xiSliceHeatTransfer lam 0 t N).re := pos_of_mul_pos_right hT hsq.le
  exact Complex.lt_def.mpr ⟨hTre, (DeBruijn.xiSliceHeatTransfer_im_eq_zero hlam0.le t N).symm⟩

namespace DeBruijn

/-- Heat `(133/200)/log|t|` makes every even heated slice coefficient positive
at all sufficiently large absolute heights. -/
theorem exists_xiSliceHeatTransfer_pos_heat_subWeyl :
    ∃ t₀ : ℝ, 80 ≤ t₀ ∧ ∀ t : ℝ, t₀ ≤ |t| → ∀ lam : ℝ,
      (133 / 200) / Real.log |t| ≤ lam → ∀ m : ℕ,
        0 < xiSliceHeatTransfer lam 0 t (2 * m) := by
  apply exists_xiSliceHeatTransfer_pos_heat_of_at_heat (by norm_num)
  apply exists_xiSliceHeatTransfer_pos_at_heat_of_low_order (by norm_num)
  apply exists_xiSliceHeatTransfer_pos_low_order_subWeyl (κ := 133 / 200)
    (η := 1 / 100000) (ω := 1 / 1000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  all_goals norm_num [subWeylRateOne, subWeylRateTwo, subWeylRateThree, subWeylRateFour, subWeylGain]

end DeBruijn
end RHTower

#print axioms RHTower.DeBruijn.exists_xiSliceHeatTransfer_pos_heat_subWeyl
