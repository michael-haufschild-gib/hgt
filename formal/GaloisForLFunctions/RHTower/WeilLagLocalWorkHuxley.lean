import GaloisForLFunctions.RHTower.WeilLagLocalChebyshevChord
import GaloisForLFunctions.RHTower.PrimeShortIntervalsHuxleyAsymptotic
import GaloisForLFunctions.RHTower.PrimeAlmostAllShortIntervals
import GaloisForLFunctions.RHTower.PoleSelfEnergyLimit

/-!
# The signed local work of a quadratic mesh is `o(√k)`

The centered chord certificate (`integerLag_local_chebyshev_upper_interpolation`) bounds an interior
lag by the endpoint lags plus `W/√k`, where for every constant `c`

`W = u n ∫_n^k (E(t) - c) t^{-2} dt - v m ∫_k^m (E(t) - c) t^{-2} dt`,  `E(t) = ψ(t) - t`.

With `c = E(k)` the integrands are short-window errors `ψ(k) - ψ(t) - (k - t)` and
`ψ(t) - ψ(k) - (t - k)`.  Huxley's short-interval prime number theorem, made uniform over all window
lengths `h ∈ [x^α, x/2]` (`eventually_abs_psi_window_sub_le`, `α = 2/3`), bounds them by `ε|t - k|`;
shorter windows cost at most `3k^α log(2k)`.  On a mesh with `(m - n)² ≤ C k^{3/2}`,
`k/2 ≤ n ≤ k ≤ m ≤ 2k`, this gives `|W| ≤ 4εC√k + 12√C k^{α - 1/4} log(2k) = o(√k)`, hence

`a_k ≤ max(0, a_n, a_m) + ε`   for all large `k`.

Upper lag bounds therefore propagate from any quadratic integer mesh to all integers with `o(1)`
loss (the quadratic interpolation `integerLag_curvature_upper_interpolation` loses a constant).
-/

open MeasureTheory Set Filter Topology
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-- The short-window zero weight is monotone in its cutoff. -/
theorem zeroShortWeight_mono {x Y Y' : ℝ} (hx : 0 ≤ x) (hYY : Y ≤ Y') (ρ : ℂ) :
    zeroShortWeight x Y ρ ≤ zeroShortWeight x Y' ρ := by
  unfold zeroShortWeight
  refine mul_le_mul_of_nonneg_left (min_le_min_left _ ?_) (Real.rpow_nonneg hx _)
  exact div_le_div_of_nonneg_right hYY (by positivity)

theorem tsum_zeroShortWeight_mono {x Y Y' : ℝ} (hx : 1 ≤ x) (hY : 0 ≤ Y) (hYY : Y ≤ Y') :
    ∑' q : XiZeroCopy, zeroShortWeight x Y (q.1 : ℂ)
      ≤ ∑' q : XiZeroCopy, zeroShortWeight x Y' (q.1 : ℂ) :=
  (summable_zeroShortWeight hx hY).tsum_le_tsum
    (fun q => zeroShortWeight_mono (by linarith) hYY _)
    (summable_zeroShortWeight hx (hY.trans hYY))

/-- `C x²/(h · h/M) ≤ CM x^{2(1-α)}` once `x^α ≤ h`. -/
theorem sq_div_window_le {x α C M h : ℝ} (hx : 0 < x) (hC : 0 ≤ C) (hM : 0 < M)
    (hh : x ^ α ≤ h) :
    C * x ^ 2 / (h * (h / M)) ≤ C * M * x ^ (2 * (1 - α)) := by
  have hxa : 0 < x ^ α := Real.rpow_pos_of_pos hx α
  have hh0 : 0 < h := lt_of_lt_of_le hxa hh
  have e1 : x ^ (2 * (1 - α)) = x ^ 2 / (x ^ α * x ^ α) := by
    rw [show 2 * (1 - α) = (2 : ℝ) - α - α by ring, Real.rpow_sub hx, Real.rpow_sub hx,
      Real.rpow_two]
    field_simp
  have e : C * M * x ^ (2 * (1 - α)) = C * x ^ 2 / (x ^ α * (x ^ α / M)) := by
    rw [e1]; field_simp
  rw [e]
  refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
  exact mul_le_mul hh (div_le_div_of_nonneg_right hh hM.le) (by positivity) hh0.le

/-- **Huxley's short-interval prime number theorem, uniform in the window.**  For `7/12 < α < 1`
and `ε > 0`, eventually `|ψ(x + h) - ψ(x) - h| ≤ εh` for every `h ∈ [x^α, x/2]`. -/
theorem eventually_abs_psi_window_sub_le {α ε : ℝ} (hα : 7 / 12 < α) (hα1 : α < 1) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ h : ℝ, x ^ α ≤ h → h ≤ x / 2 →
      |Chebyshev.psi (x + h) - Chebyshev.psi x - h| ≤ ε * h := by
  have hu : 0 < 1 - α := by linarith
  have hu' : 1 - α < 5 / 12 := by linarith
  obtain ⟨M, hM⟩ : ∃ M : ℕ, 6 / ε < M ∧ 4 ≤ M := by
    obtain ⟨M, hM⟩ := exists_nat_gt (max (6 / ε) 4)
    exact ⟨M, lt_of_le_of_lt (le_max_left _ _) hM,
      by exact_mod_cast (lt_of_le_of_lt (le_max_right _ _) hM).le⟩
  have hMR : (4 : ℝ) ≤ M := by exact_mod_cast hM.2
  have hM0 : (0 : ℝ) < M := by linarith
  have hMe : 2 / (M : ℝ) ≤ ε / 3 := by
    rw [div_le_iff₀ hM0]
    have := hM.1
    rw [div_lt_iff₀ hε] at this
    linarith
  have hz8 := (tendsto_tsum_zeroShortWeight_seven_twelfths (u := 1 - α) (c := 8 * M) hu hu'
    (by linarith)).eventually (gt_mem_nhds (show (0 : ℝ) < ε / 24 by positivity))
  have hz4 := (tendsto_tsum_zeroShortWeight_seven_twelfths (u := 1 - α) (c := 4 * M) hu hu'
    (by linarith)).eventually (gt_mem_nhds (show (0 : ℝ) < ε / 24 by positivity))
  have hsmall : Tendsto (fun x : ℝ => 4 * (M : ℝ) * x ^ (-(1 + 2 * α))) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (by linarith : (0 : ℝ) < 1 + 2 * α)).const_mul
      (4 * (M : ℝ))
  have h4 := hsmall.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 3 by positivity))
  filter_upwards [hz8, hz4, h4, eventually_ge_atTop (4 : ℝ)] with x hz8x hz4x h4x hx4 h hxh hhx
  have hx0 : 0 < x := by linarith
  have hxa : 0 < x ^ α := Real.rpow_pos_of_pos hx0 α
  have hh0 : 0 < h := lt_of_lt_of_le hxa hxh
  have hh' : 0 < h / M := div_pos hh0 hM0
  have h2h' : 2 * (h / M) ≤ h := by
    rw [mul_div_assoc', div_le_iff₀ hM0]; nlinarith
  have hx1 : (1 : ℝ) ≤ x := by linarith
  -- the zero sums at the window are dominated by those at `x^α`
  have hY8 := tsum_zeroShortWeight_mono hx1 (by positivity)
    (sq_div_window_le hx0 (by norm_num : (0 : ℝ) ≤ 8) hM0 hxh)
  have hY4 := tsum_zeroShortWeight_mono hx1 (by positivity)
    (sq_div_window_le hx0 (by norm_num : (0 : ℝ) ≤ 4) hM0 hxh)
  -- the boundary term `4/(x h') ≤ (ε/3) h`
  have hterm : 4 / (x * (h / M)) ≤ ε / 3 * h := by
    have hxa2 : x ^ α * x ^ α ≤ h * h := mul_le_mul hxh hxh hxa.le hh0.le
    have e : 4 * (M : ℝ) * x ^ (-(1 + 2 * α)) = 4 * M / (x * (x ^ α * x ^ α)) := by
      rw [Real.rpow_neg hx0.le, Real.rpow_add hx0, Real.rpow_one, Real.rpow_mul hx0.le,
        show (x ^ (2 : ℝ)) ^ α = x ^ α * x ^ α by
          rw [← Real.rpow_mul hx0.le, mul_comm, Real.rpow_mul hx0.le, Real.rpow_two]; ring]
      field_simp
    rw [e] at h4x
    have hle : 4 / (x * (h / M)) ≤ 4 * M / (x * (x ^ α * x ^ α)) * h := by
      have e2 : 4 / (x * (h / M)) = 4 * M / (x * h) := by field_simp
      rw [e2, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
      have h0 : 0 ≤ 4 * (M : ℝ) * x := by positivity
      calc 4 * (M : ℝ) * (x * (x ^ α * x ^ α)) = (4 * M * x) * (x ^ α * x ^ α) := by ring
        _ ≤ (4 * M * x) * (h * h) := mul_le_mul_of_nonneg_left hxa2 h0
        _ = 4 * M * h * (x * h) := by ring
    exact hle.trans (mul_le_mul_of_nonneg_right h4x.le hh0.le)
  have hlow := psi_window_ge_sub_zeroShortWeight (x := x) (h := h) (h' := h / M) (by linarith)
    hh' h2h' (by linarith)
  have hup := psi_window_le_add_zeroShortWeight (x := x) (h := h) (h' := h / M) hx4 hh' h2h' hhx
  rw [show 8 * x ^ 2 / (h * (h / M)) = 8 * x ^ 2 / (h * (h / M)) from rfl] at hlow
  have hS8 : ∑' q : XiZeroCopy, zeroShortWeight x (8 * x ^ 2 / (h * (h / M))) (q.1 : ℂ)
      ≤ ε / 24 := by
    have := hY8.trans hz8x.le
    simpa [mul_assoc] using this
  have hS4 : ∑' q : XiZeroCopy, zeroShortWeight x (4 * x ^ 2 / (h * (h / M))) (q.1 : ℂ)
      ≤ ε / 24 := by
    have := hY4.trans hz4x.le
    simpa [mul_assoc] using this
  have hMh : 2 * (h / M) ≤ ε / 3 * h := by
    have := mul_le_mul_of_nonneg_right hMe hh0.le
    rw [div_mul_eq_mul_div] at this
    rw [mul_div_assoc']
    linarith
  have hS8' := mul_le_mul_of_nonneg_left hS8 (by positivity : (0 : ℝ) ≤ 2 * h)
  have hS4' := mul_le_mul_of_nonneg_left hS4 (by positivity : (0 : ℝ) ≤ 8 * h)
  rw [abs_le]
  constructor <;> nlinarith

/-- The trivial short-window bound `|ψ(t+L) - ψ(t) - L| ≤ L + (L+1) log(t+L)`. -/
theorem abs_psi_window_sub_le_trivial {t L : ℝ} (ht : 1 ≤ t) (hL : 0 ≤ L) :
    |Chebyshev.psi (t + L) - Chebyshev.psi t - L| ≤ L + (L + 1) * Real.log (t + L) := by
  have hsum := psi_sub_psi_eq_sum (a := t) (b := t + L) (by linarith)
  have hlog0 : 0 ≤ Real.log (t + L) := Real.log_nonneg (by linarith)
  have hnn : 0 ≤ Chebyshev.psi (t + L) - Chebyshev.psi t := by
    rw [hsum]; exact Finset.sum_nonneg fun n _ => ArithmeticFunction.vonMangoldt_nonneg
  have hle : Chebyshev.psi (t + L) - Chebyshev.psi t ≤ (L + 1) * Real.log (t + L) := by
    rw [hsum]
    calc ∑ n ∈ Finset.Ioc ⌊t⌋₊ ⌊t + L⌋₊, ArithmeticFunction.vonMangoldt n
        ≤ ∑ _n ∈ Finset.Ioc ⌊t⌋₊ ⌊t + L⌋₊, Real.log (t + L) := by
          refine Finset.sum_le_sum fun n hn => ?_
          have hn' := Finset.mem_Ioc.mp hn
          have hn1 : (n : ℝ) ≤ t + L := by
            have := Nat.floor_le (show 0 ≤ t + L by linarith)
            have : (n : ℝ) ≤ ⌊t + L⌋₊ := by exact_mod_cast hn'.2
            linarith
          have hnpos : (0 : ℝ) < n := by
            have : (0 : ℕ) < n := lt_of_le_of_lt (Nat.zero_le _) hn'.1
            exact_mod_cast this
          exact (ArithmeticFunction.vonMangoldt_le_log).trans (Real.log_le_log hnpos hn1)
      _ = ((⌊t + L⌋₊ - ⌊t⌋₊ : ℕ) : ℝ) * Real.log (t + L) := by
          rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]
      _ ≤ (L + 1) * Real.log (t + L) := by
          refine mul_le_mul_of_nonneg_right ?_ hlog0
          have h1 : ((⌊t + L⌋₊ - ⌊t⌋₊ : ℕ) : ℝ) ≤ (⌊t + L⌋₊ : ℝ) - ⌊t⌋₊ := by
            rw [Nat.cast_sub (Nat.floor_le_floor (by linarith))]
          have h2 := Nat.floor_le (show 0 ≤ t + L by linarith)
          have h3 := Nat.lt_floor_add_one t
          linarith
  rw [abs_le]; constructor <;> linarith


/-! ## The local work -/

/-- The short-window error between `t` and `k`, for `|t - k| ≤ k/4`, `k/2 ≤ t`, both above the
uniform Huxley threshold `X₀`: at most `ε|t - k|` for windows longer than `k^{2/3}`, otherwise at
most `3k^{2/3}(1 + log 2k)`. -/
theorem abs_chebyshevError_sub_le_window {ε X₀ : ℝ}
    (hX : ∀ x : ℝ, X₀ ≤ x → ∀ h : ℝ, x ^ (2 / 3 : ℝ) ≤ h → h ≤ x / 2 →
      |Chebyshev.psi (x + h) - Chebyshev.psi x - h| ≤ ε * h)
    (hε : 0 ≤ ε) {k t : ℝ} (hk : 4 ≤ k) (hkX : X₀ ≤ k / 2) (ht : k / 2 ≤ t)
    (htk : |t - k| ≤ k / 4) :
    |chebyshevError t - chebyshevError k|
      ≤ ε * |t - k| + 3 * k ^ (2 / 3 : ℝ) * (1 + Real.log (2 * k)) := by
  have hk0 : 0 < k := by linarith
  have hka : 1 ≤ k ^ (2 / 3 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hlog2k : 0 ≤ Real.log (2 * k) := Real.log_nonneg (by linarith)
  have hB : 0 ≤ 3 * k ^ (2 / 3 : ℝ) * (1 + Real.log (2 * k)) := by positivity
  unfold chebyshevError
  rcases le_total t k with htk' | hkt
  · -- window `(t, k]` with base `t`
    set L := k - t with hL
    have hL0 : 0 ≤ L := by rw [hL]; linarith
    have habs : |t - k| = L := by rw [abs_of_nonpos (by linarith), hL]; ring
    have heq : Chebyshev.psi t - t - (Chebyshev.psi k - k)
        = -(Chebyshev.psi (t + L) - Chebyshev.psi t - L) := by rw [hL]; ring_nf
    rw [heq, abs_neg, habs]
    have ht1 : 1 ≤ t := by linarith
    rcases le_or_gt (t ^ (2 / 3 : ℝ)) L with hlong | hshort
    · have := hX t (by linarith) L hlong (by rw [abs_of_nonpos (by linarith)] at htk; linarith)
      linarith
    · have htriv := abs_psi_window_sub_le_trivial ht1 hL0
      have hta : t ^ (2 / 3 : ℝ) ≤ k ^ (2 / 3 : ℝ) :=
        Real.rpow_le_rpow (by linarith) htk' (by norm_num)
      have hlog : Real.log (t + L) ≤ Real.log (2 * k) :=
        Real.log_le_log (by linarith) (by rw [hL]; linarith)
      have hLk : L ≤ k ^ (2 / 3 : ℝ) := by linarith
      have h1 : (L + 1) * Real.log (t + L) ≤ (2 * k ^ (2 / 3 : ℝ)) * Real.log (2 * k) := by
        have hl0 : 0 ≤ Real.log (t + L) := Real.log_nonneg (by linarith)
        exact mul_le_mul (by linarith) hlog hl0 (by positivity)
      have : 0 ≤ ε * L := mul_nonneg hε hL0
      nlinarith
  · -- window `(k, t]` with base `k`
    set L := t - k with hL
    have hL0 : 0 ≤ L := by rw [hL]; linarith
    have habs : |t - k| = L := by rw [abs_of_nonneg (by linarith)]
    have heq : Chebyshev.psi t - t - (Chebyshev.psi k - k)
        = Chebyshev.psi (k + L) - Chebyshev.psi k - L := by rw [hL]; ring_nf
    rw [heq, habs]
    have hk1 : 1 ≤ k := by linarith
    rcases le_or_gt (k ^ (2 / 3 : ℝ)) L with hlong | hshort
    · have := hX k (by linarith) L hlong (by rw [abs_of_nonneg (by linarith)] at htk; linarith)
      linarith
    · have htriv := abs_psi_window_sub_le_trivial hk1 hL0
      have hlog : Real.log (k + L) ≤ Real.log (2 * k) :=
        Real.log_le_log (by linarith) (by
          rw [abs_of_nonneg (by linarith)] at htk; linarith)
      have h1 : (L + 1) * Real.log (k + L) ≤ (2 * k ^ (2 / 3 : ℝ)) * Real.log (2 * k) := by
        have hl0 : 0 ≤ Real.log (k + L) := Real.log_nonneg (by linarith)
        exact mul_le_mul (by linarith) hlog hl0 (by positivity)
      have : 0 ≤ ε * L := mul_nonneg hε hL0
      nlinarith

/-- **The local work bound.**  On `k/2 ≤ n ≤ k ≤ m ≤ 2k` with `m - n ≤ k/4`, above the uniform
Huxley threshold, `|W| ≤ 2(m - n)(ε(m - n) + B)/k` with `B = 3k^{2/3}(1 + log 2k)`. -/
theorem abs_localWork_le {ε X₀ : ℝ}
    (hX : ∀ x : ℝ, X₀ ≤ x → ∀ h : ℝ, x ^ (2 / 3 : ℝ) ≤ h → h ≤ x / 2 →
      |Chebyshev.psi (x + h) - Chebyshev.psi x - h| ≤ ε * h)
    (hε : 0 ≤ ε) {n k m : ℝ} (hk : 4 ≤ k) (hkX : X₀ ≤ k / 2) (hn : k / 2 ≤ n) (hnk : n ≤ k)
    (hkm : k ≤ m) (hmn : m - n ≤ k / 4) {u v : ℝ} (hu0 : 0 ≤ u) (hv0 : 0 ≤ v) (huv : u + v = 1) :
    |u * n * (∫ t in Ioc n k, (chebyshevError t - chebyshevError k) / t ^ 2)
      - v * m * (∫ t in Ioc k m, (chebyshevError t - chebyshevError k) / t ^ 2)|
      ≤ 2 * (m - n) * (ε * (m - n) + 3 * k ^ (2 / 3 : ℝ) * (1 + Real.log (2 * k))) / k := by
  set B : ℝ := ε * (m - n) + 3 * k ^ (2 / 3 : ℝ) * (1 + Real.log (2 * k)) with hBdef
  have hk0 : 0 < k := by linarith
  have hn0 : 0 < n := by linarith
  have hlog2k : 0 ≤ Real.log (2 * k) := Real.log_nonneg (by linarith)
  have hB0 : 0 ≤ B := by
    rw [hBdef]
    have : 0 ≤ ε * (m - n) := mul_nonneg hε (by linarith)
    have : 0 ≤ k ^ (2 / 3 : ℝ) := Real.rpow_nonneg hk0.le _
    positivity
  have hpt : ∀ t, n ≤ t → t ≤ m → |chebyshevError t - chebyshevError k| ≤ B := by
    intro t hnt htm
    have hw := abs_chebyshevError_sub_le_window hX hε (t := t) hk hkX (by linarith)
      (by rw [abs_le]; constructor <;> linarith)
    have hd : |t - k| ≤ m - n := by rw [abs_le]; constructor <;> linarith
    have := mul_le_mul_of_nonneg_left hd hε
    rw [hBdef]; linarith
  have hI1 : ‖∫ t in Ioc n k, (chebyshevError t - chebyshevError k) / t ^ 2‖
      ≤ B / n ^ 2 * (k - n) := by
    have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc n k)
      (f := fun t => (chebyshevError t - chebyshevError k) / t ^ 2) (C := B / n ^ 2)
      (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top) (fun t ht => by
        have ht' := ht
        show ‖(chebyshevError t - chebyshevError k) / t ^ 2‖ ≤ B / n ^ 2
        rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos (lt_trans hn0 ht'.1) 2)]
        have hnt : n ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ hn0.le ht'.1.le 2
        calc |chebyshevError t - chebyshevError k| / t ^ 2
            ≤ B / t ^ 2 :=
              div_le_div_of_nonneg_right (hpt t ht'.1.le (by linarith [ht'.2]))
              (pow_pos (lt_trans hn0 ht'.1) 2).le
          _ ≤ B / n ^ 2 := div_le_div_of_nonneg_left hB0 (by positivity) hnt)
    rwa [Real.volume_real_Ioc_of_le hnk] at h
  have hI2 : ‖∫ t in Ioc k m, (chebyshevError t - chebyshevError k) / t ^ 2‖
      ≤ B / k ^ 2 * (m - k) := by
    have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc k m)
      (f := fun t => (chebyshevError t - chebyshevError k) / t ^ 2) (C := B / k ^ 2)
      (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top) (fun t ht => by
        have ht' := ht
        show ‖(chebyshevError t - chebyshevError k) / t ^ 2‖ ≤ B / k ^ 2
        rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos (lt_trans hk0 ht'.1) 2)]
        have hkt : k ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ hk0.le ht'.1.le 2
        calc |chebyshevError t - chebyshevError k| / t ^ 2
            ≤ B / t ^ 2 := div_le_div_of_nonneg_right
              (hpt t (by linarith [ht'.1]) ht'.2) (pow_pos (lt_trans hk0 ht'.1) 2).le
          _ ≤ B / k ^ 2 := div_le_div_of_nonneg_left hB0 (by positivity) hkt)
    rwa [Real.volume_real_Ioc_of_le hkm] at h
  rw [Real.norm_eq_abs] at hI1 hI2
  have hu1 : u ≤ 1 := by linarith
  have hv1 : v ≤ 1 := by linarith
  have e1 : |u * n * ∫ t in Ioc n k, (chebyshevError t - chebyshevError k) / t ^ 2|
      ≤ 2 * (k - n) * B / k := by
    rw [abs_mul, abs_mul, abs_of_nonneg hu0, abs_of_pos hn0]
    calc u * n * |∫ t in Ioc n k, (chebyshevError t - chebyshevError k) / t ^ 2|
        ≤ 1 * n * (B / n ^ 2 * (k - n)) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hu1 hn0.le) hI1 (abs_nonneg _) (by positivity)
      _ = (k - n) * B / n := by field_simp
      _ ≤ 2 * (k - n) * B / k := by
          rw [div_le_div_iff₀ hn0 hk0]
          have : 0 ≤ (k - n) * B := mul_nonneg (by linarith) hB0
          nlinarith
  have e2 : |v * m * ∫ t in Ioc k m, (chebyshevError t - chebyshevError k) / t ^ 2|
      ≤ 2 * (m - k) * B / k := by
    have hm0 : 0 < m := by linarith
    rw [abs_mul, abs_mul, abs_of_nonneg hv0, abs_of_pos hm0]
    calc v * m * |∫ t in Ioc k m, (chebyshevError t - chebyshevError k) / t ^ 2|
        ≤ 1 * m * (B / k ^ 2 * (m - k)) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hv1 hm0.le) hI2 (abs_nonneg _) (by positivity)
      _ = m * (m - k) * B / k ^ 2 := by ring
      _ ≤ 2 * (m - k) * B / k := by
          rw [div_le_div_iff₀ (by positivity) hk0]
          have hm2 : m ≤ 2 * k := by linarith
          have h0 : 0 ≤ (m - k) * B * k := mul_nonneg (mul_nonneg (by linarith) hB0) hk0.le
          calc m * (m - k) * B * k = ((m - k) * B * k) * m := by ring
            _ ≤ ((m - k) * B * k) * (2 * k) := mul_le_mul_of_nonneg_left hm2 h0
            _ = 2 * (m - k) * B * k ^ 2 := by ring
  calc |u * n * (∫ t in Ioc n k, (chebyshevError t - chebyshevError k) / t ^ 2)
        - v * m * (∫ t in Ioc k m, (chebyshevError t - chebyshevError k) / t ^ 2)|
      ≤ |u * n * ∫ t in Ioc n k, (chebyshevError t - chebyshevError k) / t ^ 2|
        + |v * m * ∫ t in Ioc k m, (chebyshevError t - chebyshevError k) / t ^ 2| :=
        abs_sub _ _
    _ ≤ 2 * (k - n) * B / k + 2 * (m - k) * B / k := add_le_add e1 e2
    _ = 2 * (m - n) * B / k := by ring


/-- `(m - n)² ≤ C k^{3/2}` gives `m - n ≤ √C k^{3/4}`. -/
theorem sub_le_of_sq_le_rpow {C k d : ℝ} (hC : 0 ≤ C) (hk : 0 ≤ k)
    (h : d ^ 2 ≤ C * k ^ (3 / 2 : ℝ)) : d ≤ Real.sqrt C * k ^ (3 / 4 : ℝ) := by
  have hk34 : k ^ (3 / 2 : ℝ) = (k ^ (3 / 4 : ℝ)) ^ 2 := by
    rw [← Real.rpow_natCast (k ^ (3 / 4 : ℝ)) 2, ← Real.rpow_mul hk]; norm_num
  rw [hk34] at h
  have h1 : d ≤ Real.sqrt (C * (k ^ (3 / 4 : ℝ)) ^ 2) := Real.le_sqrt_of_sq_le h
  rwa [Real.sqrt_mul hC, Real.sqrt_sq (Real.rpow_nonneg hk _)] at h1

/-- The quadratic part of the local work bound: `2ε₁d²/K ≤ (ε/2)√K` with `ε₁ = ε/(4(C+1))`. -/
theorem mesh_quadratic_part {ε C K d : ℝ} (hK0 : 0 < K) (hC : 0 ≤ C) (hε : 0 < ε)
    (hmesh : d ^ 2 ≤ C * K ^ (3 / 2 : ℝ)) :
    2 * (ε / (4 * (C + 1))) * d ^ 2 / K ≤ ε / 2 * Real.sqrt K := by
  have hsqK : 0 < Real.sqrt K := Real.sqrt_pos.mpr hK0
  have hK32 : K ^ (3 / 2 : ℝ) / K = Real.sqrt K := by
    rw [Real.sqrt_eq_rpow, eq_comm, eq_div_iff hK0.ne', ← Real.rpow_add_one hK0.ne']
    norm_num
  calc 2 * (ε / (4 * (C + 1))) * d ^ 2 / K
      ≤ 2 * (ε / (4 * (C + 1))) * (C * K ^ (3 / 2 : ℝ)) / K :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hmesh (by positivity)) hK0.le
    _ = ε / 2 * (C / (C + 1)) * (K ^ (3 / 2 : ℝ) / K) := by field_simp; ring
    _ = ε / 2 * (C / (C + 1)) * Real.sqrt K := by rw [hK32]
    _ ≤ ε / 2 * Real.sqrt K := by
        have hC1 : C / (C + 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
        have := mul_le_mul_of_nonneg_left hC1 (by positivity : (0 : ℝ) ≤ ε / 2)
        nlinarith [this, hsqK]

/-- The short-window part: `2d·3K^{2/3}(1 + log 2K)/K ≤ (ε/2)√K` once `d ≤ √C K^{3/4}` and
`(log K + 2)K^{-1/12} ≤ ε/(12√C + 1)`. -/
theorem mesh_log_part {ε C K d : ℝ} (hK : 4 ≤ K) (hε : 0 < ε)
    (hd : d ≤ Real.sqrt C * K ^ (3 / 4 : ℝ))
    (hkl : (Real.log K + 2) ^ 1 * K ^ (-(1 / 12 : ℝ)) ≤ ε / (12 * Real.sqrt C + 1)) :
    2 * d * (3 * K ^ (2 / 3 : ℝ) * (1 + Real.log (2 * K))) / K ≤ ε / 2 * Real.sqrt K := by
  have hK0 : 0 < K := by linarith
  have hsqK : 0 < Real.sqrt K := Real.sqrt_pos.mpr hK0
  have hD0 : 0 < 12 * Real.sqrt C + 1 := by positivity
  have hlog2K : 1 + Real.log (2 * K) ≤ Real.log K + 2 := by
    rw [Real.log_mul (by norm_num) hK0.ne']
    have := Real.log_two_lt_d9; linarith
  have hlogpos : 0 ≤ 1 + Real.log (2 * K) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 * K by linarith); linarith
  have hK5 : K ^ (3 / 4 : ℝ) * K ^ (2 / 3 : ℝ) / K = Real.sqrt K * K ^ (-(1 / 12 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hK0, ← Real.rpow_add hK0, div_eq_iff hK0.ne',
      ← Real.rpow_add_one hK0.ne']
    norm_num
  have hneg0 : 0 < K ^ (-(1 / 12 : ℝ)) := Real.rpow_pos_of_pos hK0 _
  have h23 : 0 ≤ K ^ (2 / 3 : ℝ) := Real.rpow_nonneg hK0.le _
  have hsC := Real.sqrt_nonneg C
  calc 2 * d * (3 * K ^ (2 / 3 : ℝ) * (1 + Real.log (2 * K))) / K
      ≤ 2 * (Real.sqrt C * K ^ (3 / 4 : ℝ))
          * (3 * K ^ (2 / 3 : ℝ) * (1 + Real.log (2 * K))) / K := by
        refine div_le_div_of_nonneg_right ?_ hK0.le
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd (by norm_num))
          (by positivity)
    _ = 6 * Real.sqrt C * (1 + Real.log (2 * K)) * (K ^ (3 / 4 : ℝ) * K ^ (2 / 3 : ℝ) / K) := by
        ring
    _ = 6 * Real.sqrt C * Real.sqrt K * ((1 + Real.log (2 * K)) * K ^ (-(1 / 12 : ℝ))) := by
        rw [hK5]; ring
    _ ≤ 6 * Real.sqrt C * Real.sqrt K * (ε / (12 * Real.sqrt C + 1)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        calc (1 + Real.log (2 * K)) * K ^ (-(1 / 12 : ℝ))
            ≤ (Real.log K + 2) ^ 1 * K ^ (-(1 / 12 : ℝ)) := by
              rw [pow_one]; exact mul_le_mul_of_nonneg_right hlog2K hneg0.le
          _ ≤ ε / (12 * Real.sqrt C + 1) := hkl
    _ = (6 * Real.sqrt C / (12 * Real.sqrt C + 1)) * ε * Real.sqrt K := by ring
    _ ≤ ε / 2 * Real.sqrt K := by
        have h6 : 6 * Real.sqrt C / (12 * Real.sqrt C + 1) ≤ 1 / 2 := by
          rw [div_le_iff₀ hD0]; linarith
        have := mul_le_mul_of_nonneg_right h6 (mul_nonneg hε.le hsqK.le)
        nlinarith [this]

/-- `4√C ≤ K^{1/4}` from `16C ≤ √K`, hence `√C K^{3/4} ≤ K/4`. -/
theorem sqrt_mul_rpow_le_quarter {C K : ℝ} (hC : 0 ≤ C) (hK0 : 0 < K)
    (hkC : 16 * C ≤ K ^ (1 / 2 : ℝ)) : Real.sqrt C * K ^ (3 / 4 : ℝ) ≤ K / 4 := by
  have hK34 : K ^ (3 / 4 : ℝ) * K ^ (1 / 4 : ℝ) = K := by
    rw [← Real.rpow_add hK0]; norm_num
  have hK14 : K ^ (1 / 4 : ℝ) * K ^ (1 / 4 : ℝ) = K ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_add hK0]; norm_num
  have hsC : Real.sqrt C * Real.sqrt C = C := Real.mul_self_sqrt hC
  have h14 : 0 < K ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hK0 _
  have hsC0 := Real.sqrt_nonneg C
  have h4 : 4 * Real.sqrt C ≤ K ^ (1 / 4 : ℝ) := by
    by_contra hlt
    push Not at hlt
    have : (K ^ (1 / 4 : ℝ)) * (K ^ (1 / 4 : ℝ)) < (4 * Real.sqrt C) * (4 * Real.sqrt C) :=
      mul_self_lt_mul_self h14.le hlt
    rw [hK14] at this
    nlinarith
  have h34 : 0 ≤ K ^ (3 / 4 : ℝ) := Real.rpow_nonneg hK0.le _
  nlinarith [mul_le_mul_of_nonneg_left h4 h34]

/-- **Interior lags on a quadratic mesh.**  For every `C ≥ 0` and `ε > 0`, for all large `k`: if
`k/2 ≤ n ≤ k ≤ m`, `(m - n)² ≤ C k^{3/2}` and `k = un + vm` (`u, v ≥ 0`, `u + v = 1`), then
`a_k ≤ max(0, a_n, a_m) + ε`. -/
theorem eventually_integerLag_le_max_add_of_quadraticMesh {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, ∀ n m : ℕ, (k : ℝ) / 2 ≤ n → n ≤ k → k ≤ m →
      ((m : ℝ) - n) ^ 2 ≤ C * (k : ℝ) ^ (3 / 2 : ℝ) →
      ∀ u v : ℝ, 0 ≤ u → 0 ≤ v → u + v = 1 → (k : ℝ) = u * n + v * m →
        integerLag k ≤ max 0 (max (integerLag n) (integerLag m)) + ε := by
  have hε₁0 : 0 < ε / (4 * (C + 1)) := by positivity
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp (eventually_abs_psi_window_sub_le
    (α := 2 / 3) (by norm_num) (by norm_num) hε₁0)
  have hD0 : 0 < 12 * Real.sqrt C + 1 := by positivity
  have hlogev := (tendsto_log_add_two_pow_mul_rpow_neg 1 (show (0 : ℝ) < 1 / 12 by
    norm_num)).eventually (ge_mem_nhds (show (0 : ℝ) < ε / (12 * Real.sqrt C + 1) by positivity))
  have hreal : ∀ᶠ K : ℝ in atTop, 4 ≤ K ∧ X₀ ≤ K / 2 ∧ 16 * C ≤ K ^ (1 / 2 : ℝ) ∧
      (Real.log K + 2) ^ 1 * K ^ (-(1 / 12 : ℝ)) ≤ ε / (12 * Real.sqrt C + 1) := by
    filter_upwards [eventually_ge_atTop (4 : ℝ), eventually_ge_atTop (2 * X₀), hlogev,
      (tendsto_rpow_atTop (show (0 : ℝ) < 1 / 2 by norm_num)).eventually_ge_atTop (16 * C)]
      with K h1 h2 h3 h4
    exact ⟨h1, by linarith, h4, h3⟩
  filter_upwards [tendsto_natCast_atTop_atTop.eventually hreal] with k ⟨hk4, hkX, hkC, hkl⟩
  intro n m hn hnk hkm hmesh u v hu hv huv hmean
  have hK0 : (0 : ℝ) < k := by linarith
  have hn2 : 2 ≤ n := by
    have : (2 : ℝ) ≤ n := by linarith
    exact_mod_cast this
  have hnkR : (n : ℝ) ≤ k := by exact_mod_cast hnk
  have hkmR : (k : ℝ) ≤ m := by exact_mod_cast hkm
  have hd0 : 0 ≤ (m : ℝ) - n := by linarith
  have hd := sub_le_of_sq_le_rpow hC hK0.le hmesh
  have hmn : (m : ℝ) - n ≤ k / 4 := hd.trans (sqrt_mul_rpow_le_quarter hC hK0 hkC)
  have hcert := integerLag_local_chebyshev_upper_interpolation n k m hn2 hnk hkm u v hu hv huv
    hmean (chebyshevError k)
  have hW := abs_localWork_le (fun x hx h h1 h2 => hX₀ x hx h h1 h2) hε₁0.le (n := (n : ℝ))
    (k := (k : ℝ)) (m := (m : ℝ)) hk4 hkX hn hnkR hkmR hmn hu hv huv
  have hA := mesh_quadratic_part hK0 hC hε hmesh
  have hB := mesh_log_part hk4 hε hd hkl
  have hsqK : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr hK0
  set W := u * n * (∫ t in Ioc (n : ℝ) k, (chebyshevError t - chebyshevError k) / t ^ 2)
    - v * m * (∫ t in Ioc (k : ℝ) m, (chebyshevError t - chebyshevError k) / t ^ 2) with hWdef
  have hsplit : 2 * ((m : ℝ) - n) * (ε / (4 * (C + 1)) * ((m : ℝ) - n)
      + 3 * (k : ℝ) ^ (2 / 3 : ℝ) * (1 + Real.log (2 * k))) / k
      = 2 * (ε / (4 * (C + 1))) * ((m : ℝ) - n) ^ 2 / k
        + 2 * ((m : ℝ) - n) * (3 * (k : ℝ) ^ (2 / 3 : ℝ) * (1 + Real.log (2 * k))) / k := by ring
  have hWle : |W| ≤ ε * Real.sqrt k := by linarith
  have hWdiv : W / Real.sqrt k ≤ ε := by
    rw [div_le_iff₀ hsqK]
    exact (le_abs_self W).trans hWle
  linarith


/-- **High lags occupy one-sided blocks.**  For every `D` and `ε > 0`, for all large `k` with
`a_k > ε`: either every `n ∈ [k - Dk^{3/4}, k]` (integer, `n ≥ k/2`) has `a_n ≥ a_k - ε`, or every
`m ∈ [k, k + Dk^{3/4}]` has `a_m ≥ a_k - ε`. -/
theorem eventually_integerLag_block {D ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, ε < integerLag k →
      (∀ n : ℕ, (k : ℝ) / 2 ≤ n → n ≤ k → (k : ℝ) - n ≤ D * (k : ℝ) ^ (3 / 4 : ℝ) →
          integerLag k - ε ≤ integerLag n)
      ∨ ∀ m : ℕ, k ≤ m → (m : ℝ) - k ≤ D * (k : ℝ) ^ (3 / 4 : ℝ) →
          integerLag k - ε ≤ integerLag m := by
  filter_upwards [eventually_integerLag_le_max_add_of_quadraticMesh (C := 4 * D ^ 2) (by positivity)
    hε, eventually_gt_atTop 0] with k hk hk0 hlag
  by_contra hno
  push Not at hno
  obtain ⟨⟨n, hn, hnk, hnD, hnlow⟩, ⟨m, hkm, hmD, hmlow⟩⟩ := hno
  have hK0 : (0 : ℝ) < k := by exact_mod_cast hk0
  have hnkR : (n : ℝ) ≤ k := by exact_mod_cast hnk
  have hkmR : (k : ℝ) ≤ m := by exact_mod_cast hkm
  -- the mesh condition `(m - n)² ≤ 4D² k^{3/2}`
  have hmesh : ((m : ℝ) - n) ^ 2 ≤ 4 * D ^ 2 * (k : ℝ) ^ (3 / 2 : ℝ) := by
    have h1 : (m : ℝ) - n ≤ 2 * D * (k : ℝ) ^ (3 / 4 : ℝ) := by linarith
    have h0 : 0 ≤ (m : ℝ) - n := by linarith
    have h34 : ((k : ℝ) ^ (3 / 4 : ℝ)) ^ 2 = (k : ℝ) ^ (3 / 2 : ℝ) := by
      rw [← Real.rpow_natCast ((k : ℝ) ^ (3 / 4 : ℝ)) 2, ← Real.rpow_mul hK0.le]; norm_num
    calc ((m : ℝ) - n) ^ 2 ≤ (2 * D * (k : ℝ) ^ (3 / 4 : ℝ)) ^ 2 := pow_le_pow_left₀ h0 h1 2
      _ = 4 * D ^ 2 * (k : ℝ) ^ (3 / 2 : ℝ) := by rw [mul_pow, h34]; ring
  -- `k` is a convex combination of `n` and `m`
  rcases eq_or_lt_of_le hnkR with heq | hlt
  · -- `n = k`
    have hnk' : n = k := by exact_mod_cast heq
    rw [hnk'] at hnlow
    linarith
  · have hmn : (n : ℝ) < m := lt_of_lt_of_le hlt hkmR
    set v : ℝ := ((k : ℝ) - n) / ((m : ℝ) - n) with hv
    set u : ℝ := 1 - v with hu
    have hmn0 : 0 < (m : ℝ) - n := by linarith
    have hv0 : 0 ≤ v := div_nonneg (by linarith) hmn0.le
    have hv1 : v ≤ 1 := by rw [hv, div_le_one hmn0]; linarith
    have hmean : (k : ℝ) = u * n + v * m := by
      rw [hu, hv]; field_simp; ring
    have hcert := hk n m hn hnk hkm hmesh u v (by linarith) hv0 (by ring) hmean
    have h1 : max 0 (max (integerLag n) (integerLag m)) < integerLag k - ε := by
      refine max_lt (by linarith) (max_lt hnlow hmlow)
    linarith


/-- **The sharp lag ceiling is approached along primes.**  Unconditionally, for every `ε > 0`,
`a_p > a₁ - ε` for infinitely many primes `p`, where `a₁ = 2 + γ - log 4π`. -/
theorem frequently_prime_integerLag_gt {ε : ℝ} (hε : 0 < ε) :
    ∃ᶠ p : ℕ in atTop, p.Prime ∧ poleSharpConstant - ε < integerLag p := by
  have ha1 := poleSharpConstant_pos
  set δ : ℝ := min ε poleSharpConstant / 3 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  have hδε : 3 * δ ≤ ε := by rw [hδ]; linarith [min_le_left ε poleSharpConstant]
  have hδa : 3 * δ ≤ poleSharpConstant := by rw [hδ]; linarith [min_le_right ε poleSharpConstant]
  have hmesh := eventually_integerLag_le_max_add_of_quadraticMesh (C := 9) (by norm_num) hδ0
  have hprime := eventually_exists_prime_short_interval_seven_twelfths (α := 2 / 3) (by norm_num)
    (by norm_num)
  obtain ⟨X₁, hX₁⟩ := eventually_atTop.mp hprime
  obtain ⟨K₀, hK₀⟩ := eventually_atTop.mp hmesh
  -- size facts for large `k`
  have hsize : ∀ᶠ K : ℝ in atTop, 2 * X₁ + 2 ≤ K ∧ 4 * K ^ (2 / 3 : ℝ) ≤ K := by
    have h23 : Tendsto (fun K : ℝ => K ^ (-(1 / 3 : ℝ))) atTop (𝓝 0) :=
      tendsto_rpow_neg_atTop (by norm_num)
    filter_upwards [eventually_ge_atTop (2 * X₁ + 2), eventually_gt_atTop (0 : ℝ),
      h23.eventually (ge_mem_nhds (show (0 : ℝ) < 1 / 4 by norm_num))] with K h1 hK0 h3
    refine ⟨h1, ?_⟩
    have e : K ^ (2 / 3 : ℝ) = K * K ^ (-(1 / 3 : ℝ)) := by
      rw [← Real.rpow_one_add' hK0.le (by norm_num)]; norm_num
    rw [e]; nlinarith
  obtain ⟨K₁, hK₁⟩ := eventually_atTop.mp (tendsto_natCast_atTop_atTop.eventually hsize)
  rw [Filter.frequently_atTop]
  intro N
  obtain ⟨k, hkN, hklag⟩ := Filter.frequently_atTop.mp (frequently_integerLag_gt δ hδ0)
    (max (max K₀ K₁) (2 * N + 1))
  have hkK₀ : K₀ ≤ k := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hkN
  have hkK₁ : K₁ ≤ k := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hkN
  have hkN' : 2 * N + 1 ≤ k := le_trans (le_max_right _ _) hkN
  obtain ⟨hkX, hk23⟩ := hK₁ k hkK₁
  have hk1 : (1 : ℝ) ≤ k := by
    have : (2 * N + 1 : ℝ) ≤ k := by exact_mod_cast hkN'
    linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  have hK0 : (0 : ℝ) < k := by linarith
  have h23pos : 0 < (k : ℝ) ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hK0 _
  -- a prime just below `k` and one just above
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = (k : ℝ) - 2 * (k : ℝ) ^ (2 / 3 : ℝ) := ⟨_, rfl⟩
  have hxX : X₁ ≤ x := by rw [hx]; linarith
  have hx0 : 0 ≤ x := by rw [hx]; linarith
  have hxK : x ^ (2 / 3 : ℝ) ≤ (k : ℝ) ^ (2 / 3 : ℝ) :=
    Real.rpow_le_rpow hx0 (by rw [hx]; linarith) (by norm_num)
  obtain ⟨p, hp, hxp, hpx⟩ := hX₁ x hxX
  obtain ⟨q, hq, hKq, hqK⟩ := hX₁ (k : ℝ) (by linarith)
  have hpk : (p : ℝ) ≤ k := by linarith
  have hpk' : p ≤ k := by exact_mod_cast hpk
  have hkq' : k ≤ q := by exact_mod_cast hKq.le
  have hpK2 : (k : ℝ) / 2 ≤ p := by linarith
  have hqp : (q : ℝ) - p ≤ 3 * (k : ℝ) ^ (2 / 3 : ℝ) := by linarith
  have hmesh' : ((q : ℝ) - p) ^ 2 ≤ 9 * (k : ℝ) ^ (3 / 2 : ℝ) := by
    have h0 : 0 ≤ (q : ℝ) - p := by linarith
    have hpow : ((k : ℝ) ^ (2 / 3 : ℝ)) ^ 2 ≤ (k : ℝ) ^ (3 / 2 : ℝ) := by
      rw [← Real.rpow_natCast ((k : ℝ) ^ (2 / 3 : ℝ)) 2, ← Real.rpow_mul hK0.le]
      exact Real.rpow_le_rpow_of_exponent_le hk1 (by norm_num)
    calc ((q : ℝ) - p) ^ 2 ≤ (3 * (k : ℝ) ^ (2 / 3 : ℝ)) ^ 2 := pow_le_pow_left₀ h0 hqp 2
      _ = 9 * ((k : ℝ) ^ (2 / 3 : ℝ)) ^ 2 := by ring
      _ ≤ 9 * (k : ℝ) ^ (3 / 2 : ℝ) := by linarith
  have hpq : (p : ℝ) < q := lt_of_le_of_lt hpk hKq
  set v : ℝ := ((k : ℝ) - p) / ((q : ℝ) - p) with hv
  have hqp0 : 0 < (q : ℝ) - p := by linarith
  have hv0 : 0 ≤ v := div_nonneg (by linarith) hqp0.le
  have hv1 : v ≤ 1 := by rw [hv, div_le_one hqp0]; linarith
  have hmean : (k : ℝ) = (1 - v) * p + v * q := by rw [hv]; field_simp; ring
  have hcert := hK₀ k hkK₀ p q hpK2 hpk' hkq' hmesh' (1 - v) v (by linarith) hv0 (by ring) hmean
  -- one of `p, q` carries a large lag
  have hbig : poleSharpConstant - ε < integerLag p ∨ poleSharpConstant - ε < integerLag q := by
    by_contra hno
    push Not at hno
    have hmax : max 0 (max (integerLag p) (integerLag q)) ≤ poleSharpConstant - 2 * δ := by
      refine max_le (by linarith) (max_le (by linarith [hno.1]) (by linarith [hno.2]))
    linarith
  have hpN : N ≤ p := by
    have : (N : ℝ) ≤ p := by
      have : (2 * N + 1 : ℝ) ≤ k := by exact_mod_cast hkN'
      linarith
    exact_mod_cast this
  rcases hbig with h | h
  · exact ⟨p, hpN, hp, h⟩
  · exact ⟨q, le_trans hpN (by exact_mod_cast hpq.le), hq, h⟩

end

end RHTower
