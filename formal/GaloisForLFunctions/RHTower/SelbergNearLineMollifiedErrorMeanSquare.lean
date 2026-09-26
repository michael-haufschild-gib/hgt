import GaloisForLFunctions.RHTower.SelbergNearLineWindowConvexity
import GaloisForLFunctions.RHTower.ZetaMollifiedDisplacedWindowMeanSquare

/-!
# The mollified tail is exponentially small in the displacement right of the critical line

Let `N = ⌊U^{1/100}⌋`, `Ψ_N` the Barban–Vehov mollifier, `P_N` its von Mangoldt head and
`f_N = ζΨ_N − 1 − P_N`. There is an absolute `C` such that for every `a > 0`, for all large `U`
and every `U/4 ≤ T₁ ≤ T₂ ≤ U/2`,

`∫_{T₁}^{T₂} ‖f_N(1/2 + a/log U + it)‖² dt ≤ C e^{−(a+1)/300} (T₂ − T₁ + 2U^{99/100})`
(`exists_eventually_integral_hbMollifiedTail_rightShift_le`).

Proof: cover `[T₁, T₂]` by Gaussian windows of half-width `H = U^{99/100}` and apply three-lines
on each window between `Re s = 1/2 − 1/log U` and `Re s = 3`. On the left line the mollified gate
(with its power-saving window loss) and the von Mangoldt head give windowed mean square `≤ C₁H`
near the window; far from it the Gaussian `e^{−U^{1/50}/256}` beats the linear growth `U⁴`. On the
right line the tail is `O(1/N)`, so its windowed mean square is `16H/N²`. The interpolation weight
at `Re s = 1/2 + a/log U` is `λ ≥ (a+1)/(3 log U)`, and `(16/N²)^λ ≤ e^{−(a+1)/300}`.
-/

noncomputable section

open Complex Set MeasureTheory Filter

namespace RHTower

/-- The interpolated window bound collapses to an exponential saving in the displacement. -/
theorem rpow_window_interp_le {C₁ H N L a lam : ℝ} (hC₁ : 1 ≤ C₁) (hH : 0 < H) (hN : 0 < N)
    (hlam0 : 0 ≤ lam) (hNL : 16 / N ^ 2 ≤ Real.exp (-(L / 100)))
    (hlamL : (a + 1) / 300 ≤ lam * (L / 100)) :
    (C₁ * H) ^ (1 - lam) * (16 * H / N ^ 2) ^ lam ≤ C₁ * H * Real.exp (-((a + 1) / 300)) := by
  have hC0 : 0 ≤ C₁ := by linarith
  have h16 : (16 * H / N ^ 2) = (16 / N ^ 2) * H := by ring
  rw [h16, Real.mul_rpow hC0 hH.le, Real.mul_rpow (by positivity) hH.le]
  have hHH : H ^ (1 - lam) * H ^ lam = H := by
    rw [← Real.rpow_add hH, sub_add_cancel, Real.rpow_one]
  have hC : C₁ ^ (1 - lam) ≤ C₁ := by
    calc C₁ ^ (1 - lam) ≤ C₁ ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hC₁ (by linarith)
      _ = C₁ := Real.rpow_one C₁
  have hE : (16 / N ^ 2) ^ lam ≤ Real.exp (-((a + 1) / 300)) := by
    calc (16 / N ^ 2) ^ lam ≤ Real.exp (-(L / 100)) ^ lam :=
          Real.rpow_le_rpow (by positivity) hNL hlam0
      _ = Real.exp (-(L / 100) * lam) := (Real.exp_mul _ _).symm
      _ ≤ Real.exp (-((a + 1) / 300)) := Real.exp_le_exp.mpr (by nlinarith)
  have hp1 : 0 ≤ (16 / N ^ 2) ^ lam := by positivity
  have hp2 : 0 ≤ C₁ ^ (1 - lam) := by positivity
  calc C₁ ^ (1 - lam) * H ^ (1 - lam) * ((16 / N ^ 2) ^ lam * H ^ lam)
      = C₁ ^ (1 - lam) * (16 / N ^ 2) ^ lam * (H ^ (1 - lam) * H ^ lam) := by ring
    _ = C₁ ^ (1 - lam) * (16 / N ^ 2) ^ lam * H := by rw [hHH]
    _ ≤ C₁ * Real.exp (-((a + 1) / 300)) * H := by gcongr
    _ = C₁ * H * Real.exp (-((a + 1) / 300)) := by ring

/-- Covering an interval by windows of length `2H`. -/
theorem integral_le_of_windows {g : ℝ → ℝ} {T₁ T₂ H W : ℝ} (hH : 0 < H) (hT : T₁ ≤ T₂)
    (hg0 : ∀ t, 0 ≤ g t) (hgc : ContinuousOn g (Ici T₁)) (hW0 : 0 ≤ W)
    (hwin : ∀ j : ℕ, T₁ + 2 * j * H < T₂ →
      ∫ t in (T₁ + 2 * j * H)..(T₁ + 2 * (j + 1 : ℕ) * H), g t ≤ W) :
    ∫ t in T₁..T₂, g t ≤ ((T₂ - T₁) / (2 * H) + 1) * W := by
  set J : ℕ := ⌈(T₂ - T₁) / (2 * H)⌉₊ with hJ
  set grid : ℕ → ℝ := fun k => T₁ + 2 * k * H with hgrid
  have hx0 : 0 ≤ (T₂ - T₁) / (2 * H) := div_nonneg (by linarith) (by positivity)
  have hJge : (T₂ - T₁) / (2 * H) ≤ J := Nat.le_ceil _
  have hJlt : (J : ℝ) < (T₂ - T₁) / (2 * H) + 1 := Nat.ceil_lt_add_one hx0
  have hgridJ : T₂ ≤ grid J := by
    simp only [hgrid]
    have := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * H)).mp hJge
    linarith
  have hgrid_mono : ∀ k : ℕ, T₁ ≤ grid k := fun k => by
    simp only [hgrid]
    have : (0 : ℝ) ≤ 2 * k * H := by positivity
    linarith
  have hint : ∀ k : ℕ, IntervalIntegrable g volume (grid k) (grid (k + 1)) := by
    intro k
    refine (hgc.mono ?_).intervalIntegrable
    intro t ht
    rw [Set.uIcc_of_le (by simp only [hgrid]; push_cast; nlinarith)] at ht
    exact le_trans (hgrid_mono k) ht.1
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (f := g)
    (a := grid) (n := J) (fun k _ => hint k)
  have hgrid0 : grid 0 = T₁ := by simp [hgrid]
  rw [hgrid0] at hsum
  have hmono : ∫ t in T₁..T₂, g t ≤ ∫ t in T₁..grid J, g t := by
    refine intervalIntegral.integral_mono_interval le_rfl hT hgridJ ?_ ?_
    · exact Filter.Eventually.of_forall fun t => hg0 t
    · exact (hgc.mono fun t ht => by
        rw [Set.uIcc_of_le (hgrid_mono J)] at ht
        exact ht.1).intervalIntegrable
  rw [← hsum] at hmono
  have hbound : ∀ k ∈ Finset.range J, ∫ t in grid k..grid (k + 1), g t ≤ W := by
    intro k hk
    have hkJ : (k : ℝ) < (T₂ - T₁) / (2 * H) := (Nat.lt_ceil.mp (Finset.mem_range.mp hk))
    have hlt : grid k < T₂ := by
      simp only [hgrid]
      have := (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * H)).mp hkJ
      linarith
    have := hwin k hlt
    simpa [hgrid] using this
  calc ∫ t in T₁..T₂, g t ≤ ∑ k ∈ Finset.range J, ∫ t in grid k..grid (k + 1), g t := hmono
    _ ≤ ∑ _k ∈ Finset.range J, W := Finset.sum_le_sum hbound
    _ = J * W := by simp
    _ ≤ ((T₂ - T₁) / (2 * H) + 1) * W := mul_le_mul_of_nonneg_right hJlt.le hW0

/-- The energy of the von Mangoldt head on a left line `Re s = 1/2 − d`, `N^{2d} ≤ 2`. -/
theorem sum_hbVonMangoldtCoeff_displaced_le {N : ℕ} (hN : 1 ≤ N) {d CM : ℝ} (hd : 0 ≤ d)
    (hNd : (N : ℝ) ^ (2 * d) ≤ 2) (hlogN : 1 ≤ Real.log N)
    (hCM : ∑ k ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt k ^ (2 : ℕ) / (k : ℝ) ≤
      Real.log N * (Real.log N + CM)) :
    ∑ n ∈ Finset.Icc 1 N, ‖hbVonMangoldtCoeff N n‖ ^ 2 * (n : ℝ) ^ (2 * d - 1) ≤
      2 * (1 + |CM|) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hterm : ∀ n ∈ Finset.Icc 1 N, ‖hbVonMangoldtCoeff N n‖ ^ 2 * (n : ℝ) ^ (2 * d - 1) ≤
      2 * (ArithmeticFunction.vonMangoldt n ^ (2 : ℕ) / (n : ℝ)) / Real.log N ^ 2 := by
    intro n hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    have hnN : (n : ℝ) ≤ N := by exact_mod_cast (Finset.mem_Icc.mp hn).2
    have hn0 : (0 : ℝ) < n := by linarith
    have hpow : (n : ℝ) ^ (2 * d - 1) ≤ 2 / n := by
      rw [Real.rpow_sub hn0, Real.rpow_one, div_le_div_iff_of_pos_right hn0]
      exact (Real.rpow_le_rpow hn0.le hnN (by positivity)).trans hNd
    unfold hbVonMangoldtCoeff
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow]
    have hlog : 0 < Real.log (N : ℝ) := by linarith
    calc ArithmeticFunction.vonMangoldt n ^ 2 / Real.log N ^ 2 * (n : ℝ) ^ (2 * d - 1)
        ≤ ArithmeticFunction.vonMangoldt n ^ 2 / Real.log N ^ 2 * (2 / n) :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = 2 * (ArithmeticFunction.vonMangoldt n ^ (2 : ℕ) / (n : ℝ)) / Real.log N ^ 2 := by
          ring
  have hlog : 0 < Real.log (N : ℝ) := by linarith
  calc ∑ n ∈ Finset.Icc 1 N, ‖hbVonMangoldtCoeff N n‖ ^ 2 * (n : ℝ) ^ (2 * d - 1)
      ≤ ∑ n ∈ Finset.Icc 1 N,
        2 * (ArithmeticFunction.vonMangoldt n ^ (2 : ℕ) / (n : ℝ)) / Real.log N ^ 2 :=
        Finset.sum_le_sum hterm
    _ = 2 * (∑ n ∈ Finset.Icc 1 N,
        ArithmeticFunction.vonMangoldt n ^ (2 : ℕ) / (n : ℝ)) / Real.log N ^ 2 := by
        rw [← Finset.sum_div, ← Finset.mul_sum]
    _ ≤ 2 * (Real.log N * (Real.log N + CM)) / Real.log N ^ 2 := by gcongr
    _ = 2 * (1 + CM / Real.log N) := by field_simp
    _ ≤ 2 * (1 + |CM|) := by
        have : CM / Real.log N ≤ |CM| :=
          calc CM / Real.log N ≤ |CM| / Real.log N :=
                div_le_div_of_nonneg_right (le_abs_self CM) hlog.le
            _ ≤ |CM| := div_le_self (abs_nonneg _) hlogN
        linarith

/-- **Left window near the center**, from the mollified gate and the von Mangoldt head. -/
theorem integral_nearLineWindowField_left_gate_le {N : ℕ} {H τ σL α c₀ CM : ℝ} (hH : 3 ≤ H)
    (hσL : 3 / 8 ≤ σL) (hσL' : σL ≤ 1 / 2) (hα : 2 ≤ α) (hc₀ : 0 ≤ c₀)
    (hgate : ∫ u in α..(α + 2 * H), ‖riemannZeta ((σL : ℂ) + (u : ℂ) * I) *
        edPoly (hbCoeff N) (Finset.Icc 1 N) ((σL : ℂ) + (u : ℂ) * I)‖ ^ 2 ≤
          (c₀ + 1) * (α + 2 * H - α + 2 * α ^ ((95 : ℝ) / 100)))
    (hα95 : 2 * α ^ ((95 : ℝ) / 100) ≤ H) (hMVT : 8 * N * (1 + Real.log N) ≤ H)
    (hE : ∑ n ∈ Finset.Icc 1 N, ‖hbVonMangoldtCoeff N n‖ ^ 2 * (n : ℝ) ^ (2 * (1 / 2 - σL) - 1) ≤
      2 * (1 + |CM|)) :
    ∫ u in α..(α + 2 * H), ‖nearLineWindowField N H τ ((σL : ℂ) + (u : ℂ) * I)‖ ^ 2 ≤
      18 * (3 * (c₀ + 1) + 2 + 6 * (1 + |CM|)) * H := by
  have hH0 : 0 < H := by linarith
  have hG : ∫ u in α..(α + 2 * H), ‖riemannZeta ((σL : ℂ) + (u : ℂ) * I) *
      edPoly (hbCoeff N) (Finset.Icc 1 N) ((σL : ℂ) + (u : ℂ) * I)‖ ^ 2 ≤ (c₀ + 1) * (3 * H) := by
    refine hgate.trans (mul_le_mul_of_nonneg_left ?_ (by linarith))
    linarith
  have hpt : ∀ u : ℝ, displacedLinePt (1 / 2 - σL) u = (σL : ℂ) + (u : ℂ) * I := by
    intro u
    unfold displacedLinePt
    congr 2
    ring
  have hP : ∫ u in α..(α + 2 * H),
      ‖edPoly (hbVonMangoldtCoeff N) (Finset.Icc 1 N) ((σL : ℂ) + (u : ℂ) * I)‖ ^ 2 ≤
        3 * H * (2 * (1 + |CM|)) := by
    have hmv := integral_normSq_edPoly_displaced_le (1 / 2 - σL) (hbVonMangoldtCoeff N) N α
      (α + 2 * H)
    simp only [hpt] at hmv
    refine hmv.trans ?_
    have hE0 : 0 ≤ ∑ n ∈ Finset.Icc 1 N,
        ‖hbVonMangoldtCoeff N n‖ ^ 2 * (n : ℝ) ^ (2 * (1 / 2 - σL) - 1) :=
      Finset.sum_nonneg fun n _ => mul_nonneg (by positivity)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    calc (α + 2 * H - α + 8 * N * (1 + Real.log N)) * ∑ n ∈ Finset.Icc 1 N,
          ‖hbVonMangoldtCoeff N n‖ ^ 2 * (n : ℝ) ^ (2 * (1 / 2 - σL) - 1)
        ≤ 3 * H * ∑ n ∈ Finset.Icc 1 N,
          ‖hbVonMangoldtCoeff N n‖ ^ 2 * (n : ℝ) ^ (2 * (1 / 2 - σL) - 1) :=
          mul_le_mul_of_nonneg_right (by linarith) hE0
      _ ≤ 3 * H * (2 * (1 + |CM|)) := mul_le_mul_of_nonneg_left hE (by positivity)
  refine (integral_nearLineWindowField_left_near_le (τ := τ) hH hσL hσL' hα hG hP).trans ?_
  nlinarith [abs_nonneg CM]

/-- **Left window far from the center.** -/
theorem integral_nearLineWindowField_left_far_le {N : ℕ} {H τ CW σL y D : ℝ} (hH : 3 ≤ H)
    (hCW : 0 ≤ CW)
    (hW : ∀ z : ℂ, 1 / 4 ≤ z.re → z.re ≤ 3 → ‖nearLineField N z‖ ≤ CW * N * (1 + |z.im|))
    (hσL : 1 / 4 ≤ σL) (hσL' : σL ≤ 1 / 2) (hD0 : 0 ≤ D) (hyD : D + H ≤ |y|)
    (hkey : 16 * CW ^ 2 * N ^ 2 * (1 + |τ|) ^ 2 * H ^ 2 * Real.exp (-(D ^ 2 / H ^ 2)) ≤ 1) :
    ∫ u in (y + (τ - H))..(y + (τ - H)) + 2 * H,
      ‖nearLineWindowField N H τ ((σL : ℂ) + (u : ℂ) * I)‖ ^ 2 ≤ H := by
  have hH0 : 0 < H := by linarith
  set α : ℝ := y + (τ - H) with hαdef
  have hpt : ∀ u ∈ Icc α (α + 2 * H),
      ‖nearLineWindowField N H τ ((σL : ℂ) + (u : ℂ) * I)‖ ^ 2 ≤ 1 / 2 := by
    intro u hu
    have hdist : D ≤ |u - τ| := by
      have h1 : u - τ = y + (u - α - H) := by rw [hαdef]; ring
      have h2 : |u - α - H| ≤ H := abs_le.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩
      have h3 : |y| - |u - α - H| ≤ |y + (u - α - H)| := by
        have := abs_sub_abs_le_abs_sub y (-(u - α - H))
        rw [sub_neg_eq_add, abs_neg] at this
        exact this
      rw [h1]
      linarith
    refine (normSq_nearLineWindowField_far_le hH hCW hW hσL hσL' hD0 hdist).trans ?_
    linarith
  have hc : Continuous fun u : ℝ => ‖nearLineWindowField N H τ ((σL : ℂ) + (u : ℂ) * I)‖ ^ 2 :=
    (continuous_nearLineWindowField_line N H τ (by linarith : (0 : ℝ) < σL)).norm.pow 2
  calc ∫ u in α..α + 2 * H, ‖nearLineWindowField N H τ ((σL : ℂ) + (u : ℂ) * I)‖ ^ 2
      ≤ ∫ _u in α..α + 2 * H, (1 / 2 : ℝ) :=
        intervalIntegral.integral_mono_on (by linarith) (hc.intervalIntegrable _ _)
          intervalIntegrable_const hpt
    _ = H := by rw [intervalIntegral.integral_const, smul_eq_mul]; ring

/-- `16 C² e^{4L} e^{−e^{L/50}/256} ≤ 1` once `L ≥ 1280000 (4 + max 0 (log 16C²))`. -/
theorem sixteen_mul_exp_four_mul_exp_neg_le_one {CW L : ℝ} (hCW : 0 < CW)
    (hL : 1280000 * (4 + max 0 (Real.log (16 * CW ^ 2))) ≤ L) :
    16 * CW ^ 2 * Real.exp (4 * L) * Real.exp (-(Real.exp (L / 50) / 256)) ≤ 1 := by
  set K : ℝ := max 0 (Real.log (16 * CW ^ 2)) with hK
  have hK0 : 0 ≤ K := le_max_left _ _
  have hKle : Real.log (16 * CW ^ 2) ≤ K := le_max_right _ _
  have hL1 : 1 ≤ L := by nlinarith
  have hsq : (L / 50) ^ 2 / 2 ≤ Real.exp (L / 50) := by
    have := Real.pow_div_factorial_le_exp (x := L / 50) (by linarith) 2
    simpa using this
  have hgrow : Real.log (16 * CW ^ 2) + 4 * L ≤ Real.exp (L / 50) / 256 := by
    have h1 : (4 + K) * L ≤ L ^ 2 / 1280000 := by
      rw [le_div_iff₀ (by norm_num)]
      nlinarith
    have h2 : K + 4 * L ≤ (4 + K) * L := by nlinarith
    have h3 : (L / 50) ^ 2 / 2 / 256 = L ^ 2 / 1280000 := by ring
    linarith
  have hCW2 : 0 < 16 * CW ^ 2 := by positivity
  calc 16 * CW ^ 2 * Real.exp (4 * L) * Real.exp (-(Real.exp (L / 50) / 256))
      = Real.exp (Real.log (16 * CW ^ 2) + 4 * L - Real.exp (L / 50) / 256) := by
        rw [Real.exp_sub, Real.exp_add, Real.exp_log hCW2, Real.exp_neg]
        field_simp
    _ ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith)
    _ = 1 := Real.exp_zero

theorem exp_one_div_fifty_le_two : Real.exp (1 / 50) ≤ 2 := by
  by_contra h
  push Not at h
  have h1 := pow_le_pow_left₀ (by norm_num) h.le 50
  rw [← Real.exp_nat_mul] at h1
  norm_num at h1
  have := Real.exp_one_lt_d9
  linarith

theorem hundred_le_exp_five : (100 : ℝ) ≤ Real.exp 5 := by
  have h : Real.exp 5 = Real.exp 1 ^ 5 := by rw [← Real.exp_nat_mul]; norm_num
  have he := Real.exp_one_gt_d9
  rw [h]
  calc (100 : ℝ) ≤ 2.7 ^ 5 := by norm_num
    _ ≤ Real.exp 1 ^ 5 := pow_le_pow_left₀ (by norm_num) (by linarith) 5

/-- Size facts at the scale `U = e^L`, `H = e^{99L/100}`. -/
theorem nearLine_scale_facts {L : ℝ} (hL : 500 ≤ L) :
    6 ≤ Real.exp (99 / 100 * L) ∧ Real.exp (99 / 100 * L) ≤ Real.exp L / 32 ∧
      2 * Real.exp L ^ ((95 : ℝ) / 100) ≤ Real.exp (99 / 100 * L) ∧
      Real.exp L ^ ((1 : ℝ) / 8) ≤ Real.exp L / 16 ∧ 160 ≤ Real.exp L / 8 ∧
      64 ≤ Real.exp (L / 100) := by
  have he5 := hundred_le_exp_five
  have hE5 : Real.exp 5 ≤ Real.exp (L / 100) := Real.exp_le_exp.mpr (by linarith)
  have hrp : ∀ p : ℝ, Real.exp L ^ p = Real.exp (L * p) := fun p => by
    rw [← Real.exp_mul]
  refine ⟨?_, ?_, ?_, ?_, ?_, by linarith⟩
  · have : Real.exp 5 ≤ Real.exp (99 / 100 * L) := Real.exp_le_exp.mpr (by linarith)
    linarith
  · rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 32)]
    have h1 : Real.exp (99 / 100 * L) * Real.exp (L / 100) = Real.exp L := by
      rw [← Real.exp_add]; ring_nf
    nlinarith [Real.exp_pos (99 / 100 * L)]
  · rw [hrp]
    have h1 : Real.exp (99 / 100 * L) = Real.exp (L * (95 / 100)) * Real.exp (L / 25) := by
      rw [← Real.exp_add]; ring_nf
    have h2 : (2 : ℝ) ≤ Real.exp (L / 25) := by
      have := Real.add_one_le_exp (L / 25)
      linarith
    rw [h1]
    nlinarith [Real.exp_pos (L * (95 / 100))]
  · rw [hrp, le_div_iff₀ (by norm_num : (0 : ℝ) < 16)]
    have h1 : Real.exp (L * (1 / 8)) * Real.exp (7 / 8 * L) = Real.exp L := by
      rw [← Real.exp_add]; ring_nf
    have h2 : (16 : ℝ) ≤ Real.exp (7 / 8 * L) := by
      have := Real.add_one_le_exp (7 / 8 * L)
      linarith
    nlinarith [Real.exp_pos (L * (1 / 8))]
  · rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 8)]
    have h1 : Real.exp 5 ≤ Real.exp L := Real.exp_le_exp.mpr (by linarith)
    have h2 : Real.exp 5 * Real.exp 5 ≤ Real.exp L := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
    nlinarith

/-- Size facts for the mollifier length `N`, `e^{L/100}/2 ≤ N ≤ e^{L/100}`. -/
theorem nearLine_length_facts {N : ℕ} {L : ℝ} (hL : 500 ≤ L) (hNle : (N : ℝ) ≤ Real.exp (L / 100))
    (hNgt : Real.exp (L / 100) - 1 < N) :
    2 ≤ N ∧ 1 ≤ Real.log N ∧ 8 * N * (1 + Real.log N) ≤ Real.exp (99 / 100 * L) ∧
      (N : ℝ) ^ (2 * (1 / L)) ≤ 2 ∧ Real.exp (L / 50) / 4 ≤ (N : ℝ) ^ 2 ∧
      (N : ℝ) ^ 2 ≤ Real.exp (L / 50) := by
  have he5 := hundred_le_exp_five
  have hE5 : Real.exp 5 ≤ Real.exp (L / 100) := Real.exp_le_exp.mpr (by linarith)
  have hL0 : 0 < L := by linarith
  have hNpos : (0 : ℝ) < N := by linarith
  have hlogN1 : 1 ≤ Real.log N := by
    have h1 : Real.exp 1 ≤ N := by
      have := Real.exp_one_lt_d9
      linarith
    have := Real.log_le_log (Real.exp_pos 1) h1
    rwa [Real.log_exp] at this
  have hlogN_le : Real.log N ≤ L / 100 := by
    have := Real.log_le_log hNpos hNle
    rwa [Real.log_exp] at this
  refine ⟨?_, hlogN1, ?_, ?_, ?_, ?_⟩
  · have : (2 : ℝ) < N := by linarith
    exact_mod_cast this.le
  · have h1 : 8 * (N : ℝ) * (1 + Real.log N) ≤ 8 * Real.exp (L / 100) * (1 + L / 100) := by
      have : 0 ≤ 1 + Real.log (N : ℝ) := by linarith
      gcongr
    refine h1.trans ?_
    have h2 : Real.exp (99 / 100 * L) = Real.exp (L / 100) * Real.exp (98 / 100 * L) := by
      rw [← Real.exp_add]; ring_nf
    have h3 : 8 * (1 + L / 100) ≤ Real.exp (98 / 100 * L) := by
      have := Real.add_one_le_exp (98 / 100 * L)
      linarith
    rw [h2]
    nlinarith [Real.exp_pos (L / 100)]
  · calc (N : ℝ) ^ (2 * (1 / L)) ≤ Real.exp (L / 100) ^ (2 * (1 / L)) :=
          Real.rpow_le_rpow hNpos.le hNle (by positivity)
      _ = Real.exp (1 / 50) := by
          rw [← Real.exp_mul]
          congr 1
          field_simp
          ring
      _ ≤ 2 := exp_one_div_fifty_le_two
  · have h2 : (Real.exp (L / 100) / 2) ^ 2 = Real.exp (L / 50) / 4 := by
      rw [div_pow, ← Real.exp_nat_mul]; ring_nf
    rw [← h2]
    exact pow_le_pow_left₀ (by positivity) (by linarith) 2
  · calc (N : ℝ) ^ 2 ≤ Real.exp (L / 100) ^ 2 := pow_le_pow_left₀ hNpos.le hNle 2
      _ = Real.exp (L / 50) := by rw [← Real.exp_nat_mul]; ring_nf

/-- The Gaussian beats the growth on far left windows at the scale `U = e^L`. -/
theorem nearLine_far_key {N : ℕ} {L CW τ : ℝ} (hCW : 0 < CW)
    (hLK : 1280000 * (4 + max 0 (Real.log (16 * CW ^ 2))) ≤ L)
    (hN2 : (N : ℝ) ^ 2 ≤ Real.exp (L / 50)) (hτ : 1 + |τ| ≤ Real.exp L) :
    16 * CW ^ 2 * N ^ 2 * (1 + |τ|) ^ 2 * Real.exp (99 / 100 * L) ^ 2 *
      Real.exp (-((Real.exp L / 16) ^ 2 / Real.exp (99 / 100 * L) ^ 2)) ≤ 1 := by
  have hH2 : Real.exp (99 / 100 * L) ^ 2 = Real.exp (99 / 50 * L) := by
    rw [← Real.exp_nat_mul]; ring_nf
  have hDH : (Real.exp L / 16) ^ 2 / Real.exp (99 / 100 * L) ^ 2 = Real.exp (L / 50) / 256 := by
    have hL2 : Real.exp L ^ 2 = Real.exp (L / 50) * Real.exp (99 / 50 * L) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      push_cast
      ring
    rw [hH2, div_pow, hL2]
    field_simp
    ring
  have hprod : (N : ℝ) ^ 2 * (1 + |τ|) ^ 2 * Real.exp (99 / 100 * L) ^ 2 ≤ Real.exp (4 * L) := by
    have h1 : (1 + |τ|) ^ 2 ≤ Real.exp (2 * L) := by
      calc (1 + |τ|) ^ 2 ≤ Real.exp L ^ 2 := pow_le_pow_left₀ (by positivity) hτ 2
        _ = Real.exp (2 * L) := by rw [← Real.exp_nat_mul]; ring_nf
    calc (N : ℝ) ^ 2 * (1 + |τ|) ^ 2 * Real.exp (99 / 100 * L) ^ 2 ≤
          Real.exp (L / 50) * Real.exp (2 * L) * Real.exp (99 / 50 * L) := by
          rw [hH2]
          gcongr
      _ = Real.exp (4 * L) := by
          rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  have hsize := sixteen_mul_exp_four_mul_exp_neg_le_one hCW hLK
  rw [hDH]
  have hE := Real.exp_pos (-(Real.exp (L / 50) / 256))
  calc 16 * CW ^ 2 * N ^ 2 * (1 + |τ|) ^ 2 * Real.exp (99 / 100 * L) ^ 2 *
        Real.exp (-(Real.exp (L / 50) / 256))
      = 16 * CW ^ 2 * ((N : ℝ) ^ 2 * (1 + |τ|) ^ 2 * Real.exp (99 / 100 * L) ^ 2) *
        Real.exp (-(Real.exp (L / 50) / 256)) := by ring
    _ ≤ 16 * CW ^ 2 * Real.exp (4 * L) * Real.exp (-(Real.exp (L / 50) / 256)) := by gcongr
    _ ≤ 1 := hsize

/-- **Left windows at the scale `U = e^L`** have windowed mean square `≤ C₁ H`. -/
theorem nearLine_left_window_le {N : ℕ} {L c₀ CW CM τ : ℝ} (hc₀ : 0 ≤ c₀) (hCW : 0 < CW)
    (hW : ∀ z : ℂ, 1 / 4 ≤ z.re → z.re ≤ 3 → ‖nearLineField N z‖ ≤ CW * N * (1 + |z.im|))
    (hCM : ∑ k ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt k ^ (2 : ℕ) / (k : ℝ) ≤
      Real.log N * (Real.log N + CM))
    (hL500 : 500 ≤ L) (hLK : 1280000 * (4 + max 0 (Real.log (16 * CW ^ 2))) ≤ L)
    (hNle : (N : ℝ) ≤ Real.exp (L / 100)) (hNgt : Real.exp (L / 100) - 1 < N)
    (hgU : ∀ d : ℝ, 0 < d → d ≤ 1 / 8 → 1 ≤ d * L → d * L ≤ 2 * 1 →
      ∀ a' v : ℝ, 20 ≤ a' → Real.exp L ^ ((1 : ℝ) / 8) ≤ a' → a' ≤ v → v ≤ 2 * a' →
        v ≤ Real.exp L →
        (∫ τ in a'..v, ‖riemannZeta (displacedLinePt d τ) *
          edPoly (hbCoeff N) (Finset.Icc 1 N) (displacedLinePt d τ)‖ ^ 2) ≤
            (c₀ + 1) * (v - a' + 2 * a' ^ ((95 : ℝ) / 100)))
    (hτ1 : Real.exp L / 4 ≤ τ) (hτ2 : τ ≤ Real.exp L / 2 + Real.exp (99 / 100 * L)) (y : ℝ) :
    ∫ t in (τ - Real.exp (99 / 100 * L))..(τ + Real.exp (99 / 100 * L)),
      ‖nearLineWindowField N (Real.exp (99 / 100 * L)) τ
        (((1 / 2 - 1 / L : ℝ) : ℂ) + ((y + t : ℝ) : ℂ) * I)‖ ^ 2 ≤
        (18 * (3 * (c₀ + 1) + 2 + 6 * (1 + |CM|)) + 1) * Real.exp (99 / 100 * L) := by
  obtain ⟨hH6, hHU, hU95, hU8, hU160, -⟩ := nearLine_scale_facts hL500
  obtain ⟨hN2, hlogN1, hMVT, hNd, -, hN2U⟩ := nearLine_length_facts hL500 hNle hNgt
  obtain ⟨H, hHdef⟩ : ∃ H : ℝ, H = Real.exp (99 / 100 * L) := ⟨_, rfl⟩
  obtain ⟨U, hUdef⟩ : ∃ U : ℝ, U = Real.exp L := ⟨_, rfl⟩
  rw [← hHdef] at hH6 hHU hU95 hMVT hτ2 ⊢
  rw [← hUdef] at hHU hU95 hU8 hU160 hτ1 hτ2 hgU
  have hL0 : 0 < L := by linarith
  have hH0 : 0 < H := by linarith
  have h1L0 : 0 < 1 / L := by positivity
  have h1L : 1 / L ≤ 1 / 500 := by
    rw [div_le_div_iff₀ hL0 (by norm_num)]; linarith
  have hsubst := intervalIntegral.integral_comp_add_left
    (fun u : ℝ => ‖nearLineWindowField N H τ (((1 / 2 - 1 / L : ℝ) : ℂ) + (u : ℂ) * I)‖ ^ 2) y
    (a := τ - H) (b := τ + H)
  rw [hsubst, show y + (τ + H) = (y + (τ - H)) + 2 * H by ring]
  have hC₁ : 0 ≤ 18 * (3 * (c₀ + 1) + 2 + 6 * (1 + |CM|)) := by positivity
  rcases le_or_gt |y| (U / 8) with hy | hy
  · have hyabs := abs_le.mp hy
    have hα2 : y + (τ - H) + 2 * H ≤ U := by linarith
    have hgateα := hgU (1 / L) h1L0 (by linarith)
      (by rw [one_div, inv_mul_cancel₀ hL0.ne']) (by rw [one_div, inv_mul_cancel₀ hL0.ne']; norm_num)
      (y + (τ - H)) (y + (τ - H) + 2 * H) (by linarith) (by linarith) (by linarith)
      (by linarith) hα2
    have hα95 : 2 * (y + (τ - H)) ^ ((95 : ℝ) / 100) ≤ H := by
      have : (y + (τ - H)) ^ ((95 : ℝ) / 100) ≤ U ^ ((95 : ℝ) / 100) :=
        Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
      linarith
    have hNd' : (N : ℝ) ^ (2 * (1 / 2 - (1 / 2 - 1 / L))) ≤ 2 := by
      rw [show 2 * (1 / 2 - (1 / 2 - 1 / L)) = 2 * (1 / L) by ring]
      exact hNd
    have hE := sum_hbVonMangoldtCoeff_displaced_le (by omega) (by linarith) hNd' hlogN1 hCM
    have h := integral_nearLineWindowField_left_gate_le (τ := τ) (by linarith)
      (σL := 1 / 2 - 1 / L) (by linarith) (by linarith) (by linarith) hc₀ hgateα hα95 hMVT hE
    refine h.trans ?_
    linarith
  · have hτU : 1 + |τ| ≤ Real.exp L := by
      rw [abs_of_pos (by linarith), ← hUdef]; linarith
    have hkey := nearLine_far_key hCW hLK hN2U hτU
    rw [← hHdef, ← hUdef] at hkey
    have h := integral_nearLineWindowField_left_far_le (τ := τ) (y := y) (σL := 1 / 2 - 1 / L)
      (D := U / 16) (by linarith) hCW.le hW (by linarith) (by linarith) (by linarith)
      (by linarith) hkey
    refine h.trans ?_
    nlinarith

/-- **One window at the scale `U = e^L`.** -/
theorem nearLine_window_le {N : ℕ} {L a c₀ CW CM τ : ℝ} (ha : 0 < a) (hc₀ : 0 ≤ c₀)
    (hCW : 0 < CW)
    (hW : ∀ z : ℂ, 1 / 4 ≤ z.re → z.re ≤ 3 → ‖nearLineField N z‖ ≤ CW * N * (1 + |z.im|))
    (hCM : ∑ k ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt k ^ (2 : ℕ) / (k : ℝ) ≤
      Real.log N * (Real.log N + CM))
    (hL500 : 500 ≤ L) (hLa : 2 * a + 2 ≤ L)
    (hLK : 1280000 * (4 + max 0 (Real.log (16 * CW ^ 2))) ≤ L)
    (hNle : (N : ℝ) ≤ Real.exp (L / 100)) (hNgt : Real.exp (L / 100) - 1 < N)
    (hgU : ∀ d : ℝ, 0 < d → d ≤ 1 / 8 → 1 ≤ d * L → d * L ≤ 2 * 1 →
      ∀ a' v : ℝ, 20 ≤ a' → Real.exp L ^ ((1 : ℝ) / 8) ≤ a' → a' ≤ v → v ≤ 2 * a' →
        v ≤ Real.exp L →
        (∫ τ in a'..v, ‖riemannZeta (displacedLinePt d τ) *
          edPoly (hbCoeff N) (Finset.Icc 1 N) (displacedLinePt d τ)‖ ^ 2) ≤
            (c₀ + 1) * (v - a' + 2 * a' ^ ((95 : ℝ) / 100)))
    (hτ1 : Real.exp L / 4 + Real.exp (99 / 100 * L) ≤ τ)
    (hτ2 : τ ≤ Real.exp L / 2 + Real.exp (99 / 100 * L)) :
    ∫ t in (τ - Real.exp (99 / 100 * L))..(τ + Real.exp (99 / 100 * L)),
      ‖hbMollifiedTail N (((1 / 2 + a / L : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
        2 * Real.exp 2 * ((18 * (3 * (c₀ + 1) + 2 + 6 * (1 + |CM|)) + 1) *
          Real.exp (99 / 100 * L) * Real.exp (-((a + 1) / 300))) := by
  obtain ⟨hH6, -, -, -, hU160, h64⟩ := nearLine_scale_facts hL500
  obtain ⟨hN2, -, -, -, hN2', -⟩ := nearLine_length_facts hL500 hNle hNgt
  have hL0 : 0 < L := by linarith
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have h1L : 1 / L ≤ 1 / 500 := by
    rw [div_le_div_iff₀ hL0 (by norm_num)]; linarith
  have haL : a / L ≤ 1 / 2 := by
    rw [div_le_iff₀ hL0]; linarith
  have haL0 : 0 < a / L := div_pos ha hL0
  have h1L0 : 0 < 1 / L := by positivity
  have hleft := nearLine_left_window_le hc₀ hCW hW hCM hL500 hLK hNle hNgt hgU
    (τ := τ) (by linarith) hτ2
  have h := integral_hbMollifiedTail_window_le hN2 hH6 hCW.le hW (σL := 1 / 2 - 1 / L)
    (σ₀ := 1 / 2 + a / L) (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith) (by positivity) hleft
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  have hden : 3 - (1 / 2 - 1 / L) = 5 / 2 + 1 / L := by ring
  have hnum : 1 / 2 + a / L - (1 / 2 - 1 / L) = (a + 1) / L := by ring
  rw [hden, hnum]
  have hC₁ : 1 ≤ 18 * (3 * (c₀ + 1) + 2 + 6 * (1 + |CM|)) + 1 := by
    have : 0 ≤ 18 * (3 * (c₀ + 1) + 2 + 6 * (1 + |CM|)) := by positivity
    linarith
  refine rpow_window_interp_le (L := L) (a := a) hC₁ (by linarith) hNpos (by positivity) ?_ ?_
  · rw [div_le_iff₀ (by positivity)]
    have hsplit : Real.exp (-(L / 100)) * Real.exp (L / 50) = Real.exp (L / 100) := by
      rw [← Real.exp_add]; ring_nf
    nlinarith [Real.exp_pos (-(L / 100))]
  · rw [div_div, show (a + 1) / (L * (5 / 2 + 1 / L)) * (L / 100) =
      (a + 1) / (100 * (5 / 2 + 1 / L)) by field_simp]
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    nlinarith

/-- **Core estimate** at one scale `U = e^L`, from the gate at that scale. -/
theorem integral_hbMollifiedTail_rightShift_le_core {N : ℕ} {L a c₀ CW CM T₁ T₂ : ℝ}
    (ha : 0 < a) (hc₀ : 0 ≤ c₀) (hCW : 0 < CW)
    (hW : ∀ z : ℂ, 1 / 4 ≤ z.re → z.re ≤ 3 → ‖nearLineField N z‖ ≤ CW * N * (1 + |z.im|))
    (hCM : ∑ k ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt k ^ (2 : ℕ) / (k : ℝ) ≤
      Real.log N * (Real.log N + CM))
    (hL500 : 500 ≤ L) (hLa : 2 * a + 2 ≤ L)
    (hLK : 1280000 * (4 + max 0 (Real.log (16 * CW ^ 2))) ≤ L)
    (hNle : (N : ℝ) ≤ Real.exp (L / 100)) (hNgt : Real.exp (L / 100) - 1 < N)
    (hgU : ∀ d : ℝ, 0 < d → d ≤ 1 / 8 → 1 ≤ d * L → d * L ≤ 2 * 1 →
      ∀ a' v : ℝ, 20 ≤ a' → Real.exp L ^ ((1 : ℝ) / 8) ≤ a' → a' ≤ v → v ≤ 2 * a' →
        v ≤ Real.exp L →
        (∫ τ in a'..v, ‖riemannZeta (displacedLinePt d τ) *
          edPoly (hbCoeff N) (Finset.Icc 1 N) (displacedLinePt d τ)‖ ^ 2) ≤
            (c₀ + 1) * (v - a' + 2 * a' ^ ((95 : ℝ) / 100)))
    (hT₁ : Real.exp L / 4 ≤ T₁) (hT₁₂ : T₁ ≤ T₂) (hT₂ : T₂ ≤ Real.exp L / 2) :
    ∫ t in T₁..T₂, ‖hbMollifiedTail N (((1 / 2 + a / L : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
      Real.exp 2 * (18 * (3 * (c₀ + 1) + 2 + 6 * (1 + |CM|)) + 1) *
        Real.exp (-((a + 1) / 300)) * (T₂ - T₁ + 2 * Real.exp (99 / 100 * L)) := by
  obtain ⟨hH6, -, -, -, hU160, -⟩ := nearLine_scale_facts hL500
  obtain ⟨H, hHdef⟩ : ∃ H : ℝ, H = Real.exp (99 / 100 * L) := ⟨_, rfl⟩
  have hH0 : 0 < H := by rw [hHdef]; exact Real.exp_pos _
  have hwin := fun τ (h1 : Real.exp L / 4 + Real.exp (99 / 100 * L) ≤ τ)
      (h2 : τ ≤ Real.exp L / 2 + Real.exp (99 / 100 * L)) =>
    nearLine_window_le (τ := τ) ha hc₀ hCW hW hCM hL500 hLa hLK hNle hNgt hgU h1 h2
  rw [← hHdef] at hwin ⊢
  set C₁ : ℝ := 18 * (3 * (c₀ + 1) + 2 + 6 * (1 + |CM|)) + 1 with hC₁def
  have hgc : ContinuousOn (fun t : ℝ =>
      ‖hbMollifiedTail N (((1 / 2 + a / L : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) (Ici T₁) := by
    have hT0 : 0 < T₁ := by linarith
    intro t ht
    have hne : (((1 / 2 + a / L : ℝ) : ℂ) + (t : ℂ) * I) ≠ 1 := by
      intro h
      have := congrArg Complex.im h
      simp at this
      linarith [ht.out]
    have hct : ContinuousAt (fun t : ℝ =>
        hbMollifiedTail N (((1 / 2 + a / L : ℝ) : ℂ) + (t : ℂ) * I)) t :=
      ContinuousAt.comp (g := hbMollifiedTail N)
        (f := fun t : ℝ => (((1 / 2 + a / L : ℝ) : ℂ) + (t : ℂ) * I))
        (continuousAt_hbMollifiedTail hne) (by fun_prop)
    exact (hct.norm.pow 2).continuousWithinAt
  have hW0 : (0 : ℝ) ≤ 2 * Real.exp 2 * (C₁ * H * Real.exp (-((a + 1) / 300))) := by
    have : 0 ≤ C₁ := by rw [hC₁def]; positivity
    positivity
  have hcover := integral_le_of_windows (g := fun t : ℝ =>
      ‖hbMollifiedTail N (((1 / 2 + a / L : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) hH0 hT₁₂
    (fun t => by positivity) hgc hW0
    (fun j hj => by
      have hj0 : (0 : ℝ) ≤ 2 * j * H := by positivity
      have h := hwin (T₁ + (2 * j + 1) * H) (by linarith) (by linarith)
      have e1 : T₁ + (2 * j + 1) * H - H = T₁ + 2 * j * H := by ring
      have e2 : T₁ + (2 * j + 1) * H + H = T₁ + 2 * ((j + 1 : ℕ) : ℝ) * H := by push_cast; ring
      rw [e1, e2] at h
      exact h)
  refine hcover.trans (le_of_eq ?_)
  field_simp

/-- **The mollified tail right of the critical line.** -/
theorem exists_eventually_integral_hbMollifiedTail_rightShift_le :
    ∃ C : ℝ, 0 < C ∧ ∀ a : ℝ, 0 < a → ∀ᶠ U in Filter.atTop, ∀ T₁ T₂ : ℝ,
      U / 4 ≤ T₁ → T₁ ≤ T₂ → T₂ ≤ U / 2 →
      ∫ t in T₁..T₂, ‖hbMollifiedTail (ZetaGateProductAFE.mollN U)
          (((1 / 2 + a / Real.log U : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
        C * Real.exp (-((a + 1) / 300)) * (T₂ - T₁ + 2 * U ^ ((99 : ℝ) / 100)) := by
  obtain ⟨c₀, hc₀, hgate⟩ :=
    ZetaGateProductAFE.exists_highBlock_window_bound_productAFE (R := 1) one_pos
  obtain ⟨CW, hCW, hW⟩ := exists_norm_nearLineField_le
  obtain ⟨CM, hCM⟩ := exists_sum_vonMangoldt_sq_div_le
  refine ⟨Real.exp 2 * (18 * (3 * (c₀ + 1) + 2 + 6 * (1 + |CM|)) + 1), by positivity,
    fun a ha => ?_⟩
  filter_upwards [hgate 1 one_pos, Filter.eventually_ge_atTop (Real.exp
      (max (max 500 (2 * a + 2)) (1280000 * (4 + max 0 (Real.log (16 * CW ^ 2))))))]
    with U hgU hUL₀
  intro T₁ T₂ hT₁ hT₁₂ hT₂
  have hU0 : 0 < U := lt_of_lt_of_le (Real.exp_pos _) hUL₀
  have hL := Real.log_le_log (Real.exp_pos _) hUL₀
  rw [Real.log_exp] at hL
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = Real.log U := ⟨_, rfl⟩
  have hUexp : U = Real.exp L := by rw [hLdef, Real.exp_log hU0]
  rw [← hLdef] at hL
  subst hUexp
  simp only [Real.log_exp] at hgU ⊢
  have hL500 : 500 ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hL
  have hLa : 2 * a + 2 ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hL
  have hLK : 1280000 * (4 + max 0 (Real.log (16 * CW ^ 2))) ≤ L := le_trans (le_max_right _ _) hL
  have hU100 : Real.exp L ^ ((1 : ℝ) / 100) = Real.exp (L / 100) := by
    rw [← Real.exp_mul]; ring_nf
  have hU99 : Real.exp L ^ ((99 : ℝ) / 100) = Real.exp (99 / 100 * L) := by
    rw [← Real.exp_mul]; ring_nf
  have hNle := ZetaGateProductAFE.mollN_le (Real.exp_pos L).le
  have hNgt := ZetaGateProductAFE.mollN_gt (Real.exp L)
  rw [hU100] at hNle hNgt
  obtain ⟨hN2, -⟩ := nearLine_length_facts hL500 hNle hNgt
  rw [hU99]
  exact integral_hbMollifiedTail_rightShift_le_core ha hc₀ hCW (hW _ hN2)
    (hCM _ (by omega)) hL500 hLa hLK hNle hNgt hgU hT₁ hT₁₂ hT₂

end RHTower
