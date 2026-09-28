import GaloisForLFunctions.RHTower.Sieve.RouteEAveraged

/-!
# Route E at windows longer than the square root

When the window length `h` is at least `√x`, every fibre window `[y, y + H]` of Route E starts
below its own length, so its short-interval inputs are pointwise consequences of the prime number
theorem (for `μ`) and of the square-divisor count (for `μ²` and `μ²·1_{p ∤ ·}`): a window of length
`H + 1` starting at `y ≤ 2(H+1)` deviates from its expected squarefree count by `O((H+1)^{3/4})`,
so the maximal centred mean square is `O(1/√h)`.
-/

namespace RHTower.Sieve

open Filter Topology Finset
open scoped ArithmeticFunction.Moebius

noncomputable section

/-- **The square-divisor tail of one window.**  In a window `(t, t+L]` the divisors `d > R` with
`d² ∣ n` contribute at most `L/R + √(t+1+L)` in total. -/
theorem sum_count_sq_dvd_window_le (t L R M : ℕ) (hR : 1 ≤ R) :
    (∑ d ∈ Finset.Icc (R + 1) M,
        ((((Finset.Ioc t (t + L)).filter (fun n => d ^ (2 : ℕ) ∣ n)).card : ℕ) : ℝ))
      ≤ (L : ℝ) / (R : ℝ) + ((Nat.sqrt (t + 1 + L) : ℕ) : ℝ) := by
  classical
  set S := Nat.sqrt (t + 1 + L) with hSdef
  set M' := min M S with hM'
  have hcut : (∑ d ∈ Finset.Icc (R + 1) M,
        ((((Finset.Ioc t (t + L)).filter (fun n => d ^ (2 : ℕ) ∣ n)).card : ℕ) : ℝ))
      = ∑ d ∈ Finset.Icc (R + 1) M',
        ((((Finset.Ioc t (t + L)).filter (fun n => d ^ (2 : ℕ) ∣ n)).card : ℕ) : ℝ) := by
    refine (Finset.sum_subset ?_ ?_).symm
    · intro d hd
      rw [Finset.mem_Icc] at hd ⊢
      exact ⟨hd.1, le_trans hd.2 (min_le_left _ _)⟩
    · intro d hd hnot
      rw [Finset.mem_Icc] at hd hnot
      have hlarge : Nat.sqrt (t + 1 + L) < d := by rw [hM'] at hnot; omega
      rw [count_sq_dvd_eq_zero_of_large (B := t + 1) (Nat.lt_succ_self t) hlarge]
      norm_num
  rw [hcut]
  have hterm : ∀ d ∈ Finset.Icc (R + 1) M',
      ((((Finset.Ioc t (t + L)).filter (fun n => d ^ (2 : ℕ) ∣ n)).card : ℕ) : ℝ)
        ≤ (L : ℝ) * (1 / ((d : ℝ) ^ 2)) + 1 := by
    intro d hd
    have hd0 : 0 < d ^ (2 : ℕ) := by
      rw [Finset.mem_Icc] at hd
      exact pow_pos (by omega) 2
    have h := abs_card_filter_dvd_Ioc_sub_lt (d ^ (2 : ℕ)) t (t + L) hd0 (by omega)
    have h2 := (abs_lt.mp h).2
    push_cast at h2
    have hL : ((t : ℝ) + L - t) = L := by ring
    rw [hL] at h2
    rw [mul_one_div]
    linarith
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hinv : ∑ d ∈ Finset.Icc (R + 1) M', 1 / ((d : ℝ) ^ 2) ≤ 1 / (R : ℝ) := by
    rcases le_or_gt (R + 1) M' with hle | hlt
    · have hIcc : Finset.Icc (R + 1) M' = Finset.Ico (R + 1) (M' + 1) := rfl
      rw [hIcc, Finset.sum_Ico_eq_sum_range]
      have hbase := sum_range_inv_sq_shift_le R (M' + 1 - (R + 1)) hR
      refine le_trans (le_of_eq ?_) (hbase.trans (by
        have : (0 : ℝ) ≤ 1 / (((M' + 1 - (R + 1) : ℕ) : ℝ) + R) := by positivity
        linarith))
      refine Finset.sum_congr rfl fun k _ => ?_
      push_cast; ring_nf
    · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
      positivity
  have hcard : ((Finset.Icc (R + 1) M').card : ℝ) ≤ (S : ℝ) := by
    rw [Nat.card_Icc]
    have : M' + 1 - (R + 1) ≤ S := by
      have := min_le_right M S; omega
    exact_mod_cast this
  have hL0 : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg _
  have := mul_le_mul_of_nonneg_left hinv hL0
  rw [mul_one_div] at this
  linarith


/-- The square root of a window length brackets the cut `⌊√(H+1)⌋ + 1`. -/
theorem sqrt_window_cut_bounds (H : ℕ) :
    Real.sqrt ((H : ℝ) + 1) ≤ ((Nat.sqrt (H + 1) + 1 : ℕ) : ℝ)
      ∧ ((Nat.sqrt (H + 1) + 1 : ℕ) : ℝ) ≤ Real.sqrt ((H : ℝ) + 1) + 1 := by
  have h1 := Real.real_sqrt_lt_nat_sqrt_succ (a := H + 1)
  have h2 := Real.nat_sqrt_le_real_sqrt (a := H + 1)
  push_cast at h1 h2 ⊢
  exact ⟨h1.le, by linarith⟩

/-- **The squarefree window deviation of a long window, pointwise.**  A window starting at
`y ≤ 2(H+1)` deviates from its expected squarefree count by at most `6(H+1)^{3/2}` in square. -/
theorem maxWindowDevSq_moebius_sq_le_long {y H : ℕ} (hy : 1 ≤ y) (hyH : y ≤ 2 * (H + 1)) :
    maxWindowDevSq (fun n : ℕ => ((μ n : ℤ) : ℝ) ^ (2 : ℕ)) squarefreeDensity H y
      ≤ 6 * ((H : ℝ) + 1) * Real.sqrt ((H : ℝ) + 1) := by
  set R := Nat.sqrt (H + 1) + 1 with hRdef
  have hR : 1 ≤ R := Nat.le_add_left 1 _
  have hbase := maxWindowDevSq_moebius_sq_le (y := y) (H := H) (R := R)
    (M := (y - 1) + (H + 1)) hy hR le_rfl
  have htail := sum_count_sq_dvd_window_le (y - 1) (H + 1) R ((y - 1) + (H + 1)) hR
  obtain ⟨hRlo, hRhi⟩ := sqrt_window_cut_bounds H
  rw [← hRdef] at hRlo hRhi
  set q := Real.sqrt ((H : ℝ) + 1) with hqdef
  have hH1 : (1 : ℝ) ≤ (H : ℝ) + 1 := by have : (0 : ℝ) ≤ H := Nat.cast_nonneg H; linarith
  have hq1 : 1 ≤ q := by
    have := Real.sqrt_le_sqrt hH1
    rwa [Real.sqrt_one] at this
  have hqq : q * q = (H : ℝ) + 1 := Real.mul_self_sqrt (by linarith)
  have hR0 : (0 : ℝ) < (R : ℝ) := by linarith
  have hdiv : ((H : ℝ) + 1) / (R : ℝ) ≤ q := by
    rw [div_le_iff₀ hR0]; nlinarith
  have hcast : (((H + 1 : ℕ) : ℕ) : ℝ) = (H : ℝ) + 1 := by push_cast; ring
  have hsq : ((Nat.sqrt (y - 1 + 1 + (H + 1)) : ℕ) : ℝ) ≤ 2 * q := by
    have h1 := Real.nat_sqrt_le_real_sqrt (a := y - 1 + 1 + (H + 1))
    have hle : ((y - 1 + 1 + (H + 1) : ℕ) : ℝ) ≤ 4 * ((H : ℝ) + 1) := by
      have : y - 1 + 1 + (H + 1) ≤ 4 * (H + 1) := by omega
      exact_mod_cast this
    have h2 : Real.sqrt ((y - 1 + 1 + (H + 1) : ℕ) : ℝ) ≤ Real.sqrt (4 * ((H : ℝ) + 1)) :=
      Real.sqrt_le_sqrt hle
    have h4 : Real.sqrt (4 * ((H : ℝ) + 1)) = 2 * q := by
      rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]
    linarith
  rw [hcast] at htail
  have hH0 : (0 : ℝ) ≤ (H : ℝ) + 1 := by linarith
  refine hbase.trans ?_
  have hin : (R : ℝ) + ((H : ℝ) + 1) / (R : ℝ)
      + ∑ d ∈ Finset.Icc (R + 1) ((y - 1) + (H + 1)),
          ((((Finset.Ioc (y - 1) ((y - 1) + (H + 1))).filter
            (fun n => d ^ (2 : ℕ) ∣ n)).card : ℕ) : ℝ) ≤ 6 * q := by
    have := htail
    linarith
  calc ((H : ℝ) + 1) * ((R : ℝ) + ((H : ℝ) + 1) / (R : ℝ)
        + ∑ d ∈ Finset.Icc (R + 1) ((y - 1) + (H + 1)),
            ((((Finset.Ioc (y - 1) ((y - 1) + (H + 1))).filter
              (fun n => d ^ (2 : ℕ) ∣ n)).card : ℕ) : ℝ))
      ≤ ((H : ℝ) + 1) * (6 * q) := mul_le_mul_of_nonneg_left hin hH0
    _ = 6 * ((H : ℝ) + 1) * q := by ring

/-- **The coprime squarefree window deviation of a long window, pointwise.** -/
theorem maxWindowDevSq_coprime_le_long {p : ℕ} (hp : p.Prime) {y H : ℕ} (hy : 1 ≤ y)
    (hyH : y ≤ 2 * (H + 1)) :
    maxWindowDevSq (coprimeSquarefreeWeight p) (squarefreeDensity * (p : ℝ) / ((p : ℝ) + 1)) H y
      ≤ 8 * ((H : ℝ) + 1) * Real.sqrt ((H : ℝ) + 1) := by
  set R := Nat.sqrt (H + 1) + 1 with hRdef
  have hR : 1 ≤ R := Nat.le_add_left 1 _
  have hbase := maxWindowDevSq_coprime_le hp (y := y) (H := H) (R := R)
    (M := (y - 1) + (H + 1)) hy hR le_rfl
  have htail := sum_count_sq_dvd_window_le (y - 1) (H + 1) R ((y - 1) + (H + 1)) hR
  obtain ⟨hRlo, hRhi⟩ := sqrt_window_cut_bounds H
  rw [← hRdef] at hRlo hRhi
  set q := Real.sqrt ((H : ℝ) + 1) with hqdef
  have hH1 : (1 : ℝ) ≤ (H : ℝ) + 1 := by have : (0 : ℝ) ≤ H := Nat.cast_nonneg H; linarith
  have hq1 : 1 ≤ q := by
    have := Real.sqrt_le_sqrt hH1
    rwa [Real.sqrt_one] at this
  have hqq : q * q = (H : ℝ) + 1 := Real.mul_self_sqrt (by linarith)
  have hR0 : (0 : ℝ) < (R : ℝ) := by linarith
  have hdiv : ((H : ℝ) + 1) / (R : ℝ) ≤ q := by
    rw [div_le_iff₀ hR0]; nlinarith
  have hcast : (((H + 1 : ℕ) : ℕ) : ℝ) = (H : ℝ) + 1 := by push_cast; ring
  have hsq : ((Nat.sqrt (y - 1 + 1 + (H + 1)) : ℕ) : ℝ) ≤ 2 * q := by
    have h1 := Real.nat_sqrt_le_real_sqrt (a := y - 1 + 1 + (H + 1))
    have hle : ((y - 1 + 1 + (H + 1) : ℕ) : ℝ) ≤ 4 * ((H : ℝ) + 1) := by
      have : y - 1 + 1 + (H + 1) ≤ 4 * (H + 1) := by omega
      exact_mod_cast this
    have h2 : Real.sqrt ((y - 1 + 1 + (H + 1) : ℕ) : ℝ) ≤ Real.sqrt (4 * ((H : ℝ) + 1)) :=
      Real.sqrt_le_sqrt hle
    have h4 : Real.sqrt (4 * ((H : ℝ) + 1)) = 2 * q := by
      rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]
    linarith
  rw [hcast] at htail
  have hH0 : (0 : ℝ) ≤ (H : ℝ) + 1 := by linarith
  refine hbase.trans ?_
  have hin : 2 * (R : ℝ) + ((H : ℝ) + 1) / (R : ℝ)
      + ∑ d ∈ Finset.Icc (R + 1) ((y - 1) + (H + 1)),
          ((((Finset.Ioc (y - 1) ((y - 1) + (H + 1))).filter
            (fun n => d ^ (2 : ℕ) ∣ n)).card : ℕ) : ℝ) ≤ 8 * q := by
    have := htail
    linarith
  calc ((H : ℝ) + 1) * (2 * (R : ℝ) + ((H : ℝ) + 1) / (R : ℝ)
        + ∑ d ∈ Finset.Icc (R + 1) ((y - 1) + (H + 1)),
            ((((Finset.Ioc (y - 1) ((y - 1) + (H + 1))).filter
              (fun n => d ^ (2 : ℕ) ∣ n)).card : ℕ) : ℝ))
      ≤ ((H : ℝ) + 1) * (8 * q) := mul_le_mul_of_nonneg_left hin hH0
    _ = 8 * ((H : ℝ) + 1) * q := by ring


/-- The starting points `[⌈s/2⌉, ⌈s⌉]` number at most `s` once `s ≥ 4`. -/
theorem card_Icc_half_ceil_le {s : ℝ} (hs : 4 ≤ s) :
    (((Finset.Icc ⌈s / 2⌉₊ ⌈s⌉₊).card : ℕ) : ℝ) ≤ s := by
  rw [Nat.card_Icc]
  have hA : s / 2 ≤ (⌈s / 2⌉₊ : ℝ) := Nat.le_ceil _
  have hB : (⌈s⌉₊ : ℝ) ≤ s + 1 := (Nat.ceil_lt_add_one (by linarith)).le
  have hAB : ⌈s / 2⌉₊ ≤ ⌈s⌉₊ + 1 := by
    have := Nat.ceil_le_ceil (show s / 2 ≤ s by linarith)
    omega
  have hcast : ((⌈s⌉₊ + 1 - ⌈s / 2⌉₊ : ℕ) : ℝ) = (⌈s⌉₊ : ℝ) + 1 - (⌈s / 2⌉₊ : ℝ) := by
    push_cast [Nat.cast_sub hAB]
    ring
  rw [hcast]
  linarith

/-- **Long windows: the maximal centred mean square from a pointwise `(H+1)^{3/2}` bound.**  When
the windows are at least as long as the square root of the scale, every starting point lies within
twice the window length, and a pointwise deviation bound `K(H+1)^{3/2}` gives a relative mean
square `O(1/√h)`. -/
theorem maximalWindowDevMeanSquareAt_of_long {f : ℕ → ℝ} {c : ℝ} {X hh : ℝ → ℝ}
    (hXtop : Tendsto X atTop atTop) (hgrow : Tendsto hh atTop atTop)
    (hlarge : ∀ᶠ x in atTop, Real.sqrt (X x) ≤ hh x) {K : ℝ} (hK : 0 ≤ K)
    (hpt : ∀ y H : ℕ, 1 ≤ y → y ≤ 2 * (H + 1) →
      maxWindowDevSq f c H y ≤ K * ((H : ℝ) + 1) * Real.sqrt ((H : ℝ) + 1)) :
    MaximalWindowDevMeanSquareAt f c X hh := by
  have hmaj : Tendsto (fun x => 3 * K * (1 / Real.sqrt (hh x))) atTop (𝓝 0) := by
    have := (tendsto_one_div_atTop.comp (Real.tendsto_sqrt_atTop.comp hgrow)).const_mul (3 * K)
    simpa using this
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards [hgrow.eventually_ge_atTop 1] with x hx
    have : 0 ≤ ∑ y ∈ Finset.Icc ⌈Real.sqrt (X x) / 2⌉₊ ⌈Real.sqrt (X x)⌉₊,
        maxWindowDevSq f c ⌈hh x⌉₊ y :=
      Finset.sum_nonneg fun y _ => maxWindowDevSq_nonneg f c _ y
    have : 0 < hh x := by linarith
    positivity
  · filter_upwards [hXtop.eventually_ge_atTop 16, hgrow.eventually_ge_atTop 4, hlarge]
      with x hX hh4 hle
    set s := Real.sqrt (X x) with hsdef
    set h := hh x with hhdef
    have hs4 : 4 ≤ s := by
      rw [hsdef, show (4 : ℝ) = Real.sqrt 16 by
        rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt hX
    set H := ⌈h⌉₊ with hHdef
    have hHlo : h ≤ (H : ℝ) := Nat.le_ceil _
    have hHup : (H : ℝ) ≤ h + 1 := (Nat.ceil_lt_add_one (by linarith)).le
    have hterm : ∀ y ∈ Finset.Icc ⌈s / 2⌉₊ ⌈s⌉₊,
        maxWindowDevSq f c H y ≤ K * ((H : ℝ) + 1) * Real.sqrt ((H : ℝ) + 1) := by
      intro y hy
      rw [Finset.mem_Icc] at hy
      have hy1 : 1 ≤ y := le_trans (Nat.one_le_ceil_iff.2 (by linarith)) hy.1
      have hyH : y ≤ 2 * (H + 1) := by
        have hyR : (y : ℝ) ≤ s + 1 := le_trans (by exact_mod_cast hy.2)
          (Nat.ceil_lt_add_one (by linarith)).le
        have : (y : ℝ) ≤ ((2 * (H + 1) : ℕ) : ℝ) := by push_cast; linarith
        exact_mod_cast this
      exact hpt y H hy1 hyH
    have hsum := Finset.sum_le_sum hterm
    rw [Finset.sum_const, nsmul_eq_mul] at hsum
    have hcard := card_Icc_half_ceil_le hs4
    have hH2 : (H : ℝ) + 1 ≤ 2 * h := by linarith
    have hsq2 : Real.sqrt ((H : ℝ) + 1) ≤ Real.sqrt 2 * Real.sqrt h := by
      rw [← Real.sqrt_mul (by norm_num)]; exact Real.sqrt_le_sqrt hH2
    have hsqrt2 : Real.sqrt 2 ≤ 3 / 2 := by
      rw [Real.sqrt_le_left (by norm_num)]; norm_num
    have hsh : 0 < Real.sqrt h := Real.sqrt_pos.mpr (by linarith)
    have hshh : Real.sqrt h * Real.sqrt h = h := Real.mul_self_sqrt (by linarith)
    have hpt' : K * ((H : ℝ) + 1) * Real.sqrt ((H : ℝ) + 1) ≤ 3 * K * h * Real.sqrt h := by
      have h1 : ((H : ℝ) + 1) * Real.sqrt ((H : ℝ) + 1) ≤ (2 * h) * ((3 / 2) * Real.sqrt h) := by
        refine mul_le_mul hH2 (hsq2.trans ?_) (Real.sqrt_nonneg _) (by linarith)
        exact mul_le_mul_of_nonneg_right hsqrt2 hsh.le
      calc K * ((H : ℝ) + 1) * Real.sqrt ((H : ℝ) + 1)
          = K * (((H : ℝ) + 1) * Real.sqrt ((H : ℝ) + 1)) := by ring
        _ ≤ K * ((2 * h) * ((3 / 2) * Real.sqrt h)) := mul_le_mul_of_nonneg_left h1 hK
        _ = 3 * K * h * Real.sqrt h := by ring
    have hden : 0 < h ^ (2 : ℕ) * s := by have : 0 < h := by linarith
                                          positivity
    rw [div_le_iff₀ hden]
    have hfinal : (((Finset.Icc ⌈s / 2⌉₊ ⌈s⌉₊).card : ℕ) : ℝ)
        * (K * ((H : ℝ) + 1) * Real.sqrt ((H : ℝ) + 1)) ≤ s * (3 * K * h * Real.sqrt h) := by
      have h0 : 0 ≤ K * ((H : ℝ) + 1) * Real.sqrt ((H : ℝ) + 1) := by positivity
      exact mul_le_mul hcard hpt' h0 (by linarith)
    have hid : 3 * K * (1 / Real.sqrt h) * (h ^ (2 : ℕ) * s) = s * (3 * K * h * Real.sqrt h) := by
      set q := Real.sqrt h with hq
      rw [← hshh]
      field_simp
    rw [hid]
    linarith

/-- **The Möbius first moment over long windows, from the prime number theorem.** -/
theorem maximalWindowFirstMoment_moebius_long_window {hh : ℝ → ℝ}
    (hgrow : Tendsto hh atTop atTop) (hlarge : ∀ᶠ x in atTop, Real.sqrt x ≤ hh x) :
    MaximalWindowFirstMoment (fun n : ℕ => ((μ n : ℤ) : ℝ)) hh := by
  have hZ : Tendsto (fun x => ⌈3 * hh x⌉₊) atTop atTop :=
    tendsto_nat_ceil_atTop.comp (hgrow.const_mul_atTop (by norm_num))
  have hmaj : Tendsto (fun x => 8 * (mertensSup ⌈3 * hh x⌉₊ / (⌈3 * hh x⌉₊ : ℝ))) atTop (𝓝 0) := by
    have := (tendsto_mertensSup_div.comp hZ).const_mul (8 : ℝ)
    simpa using this
  refine squeeze_zero_norm' ?_ hmaj
  filter_upwards [Filter.eventually_ge_atTop (16 : ℝ), hgrow.eventually_ge_atTop 4, hlarge]
    with x hx hh4 hle
  have hs4 : (4 : ℝ) ≤ Real.sqrt x := by
    rw [show (4 : ℝ) = Real.sqrt 16 by
      rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hx
  have hs0 : 0 < Real.sqrt x := by linarith
  set Z := ⌈3 * hh x⌉₊ with hZdef
  set H := ⌈hh x⌉₊ with hHdef
  have hZlo : 3 * hh x ≤ (Z : ℝ) := Nat.le_ceil _
  have hZhi : (Z : ℝ) ≤ 3 * hh x + 1 := (Nat.ceil_lt_add_one (by linarith)).le
  have hHup : (H : ℝ) ≤ hh x + 1 := (Nat.ceil_lt_add_one (by linarith)).le
  have hterm : ∀ y ∈ Finset.Icc ⌈Real.sqrt x / 2⌉₊ ⌈Real.sqrt x⌉₊,
      maxWindowAbs (fun n : ℕ => ((μ n : ℤ) : ℝ)) H y ≤ 2 * mertensSup Z := by
    intro y hy
    rw [Finset.mem_Icc] at hy
    have hy1 : 1 ≤ y := le_trans (Nat.one_le_ceil_iff.2 (by linarith)) hy.1
    have hyZ : y + H ≤ Z := by
      have hyB : (y : ℝ) ≤ Real.sqrt x + 1 :=
        le_trans (by exact_mod_cast hy.2) (Nat.ceil_lt_add_one (by linarith)).le
      have : ((y + H : ℕ) : ℝ) ≤ (Z : ℝ) := by push_cast; linarith
      exact_mod_cast this
    exact maxWindowAbs_moebius_le hy1 hyZ
  have hcard := card_Icc_half_ceil_le hs4
  have hsum : ∑ y ∈ Finset.Icc ⌈Real.sqrt x / 2⌉₊ ⌈Real.sqrt x⌉₊,
      maxWindowAbs (fun n : ℕ => ((μ n : ℤ) : ℝ)) H y ≤ Real.sqrt x * (2 * mertensSup Z) := by
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right hcard (by linarith [mertensSup_nonneg Z])
  have hden : (0 : ℝ) < hh x * Real.sqrt x := by have : 0 < hh x := by linarith
                                                 positivity
  have hZ0 : (0 : ℝ) < (Z : ℝ) := by linarith
  have hsum0 : 0 ≤ ∑ y ∈ Finset.Icc ⌈Real.sqrt x / 2⌉₊ ⌈Real.sqrt x⌉₊,
      maxWindowAbs (fun n : ℕ => ((μ n : ℤ) : ℝ)) H y :=
    Finset.sum_nonneg fun y _ => maxWindowAbs_nonneg _ _ y
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hsum0 hden.le), div_le_iff₀ hden]
  have hM0 := mertensSup_nonneg Z
  have hZh : (Z : ℝ) ≤ 4 * hh x := by linarith
  have key : 2 * mertensSup Z * (Z : ℝ) ≤ 8 * mertensSup Z * hh x := by nlinarith
  calc ∑ y ∈ Finset.Icc ⌈Real.sqrt x / 2⌉₊ ⌈Real.sqrt x⌉₊,
        maxWindowAbs (fun n : ℕ => ((μ n : ℤ) : ℝ)) H y
      ≤ Real.sqrt x * (2 * mertensSup Z) := hsum
    _ ≤ 8 * (mertensSup Z / (Z : ℝ)) * (hh x * Real.sqrt x) := by
        have e : 8 * (mertensSup Z / (Z : ℝ)) * (hh x * Real.sqrt x)
            = (8 * mertensSup Z * hh x / (Z : ℝ)) * Real.sqrt x := by
          field_simp
        rw [e, mul_comm (Real.sqrt x)]
        refine mul_le_mul_of_nonneg_right ?_ hs0.le
        rw [le_div_iff₀ hZ0]
        linarith


/-- The three mean-square inputs of Route E at long windows. -/
theorem routeE_longWindow_inputs {hh : ℝ → ℝ} (hhtop : Tendsto hh atTop atTop)
    (hlarge : ∀ᶠ x in atTop, Real.sqrt x ≤ hh x) :
    AveragedMeanSquare (fun n : ℕ => ((μ n : ℤ) : ℝ)) hh
      ∧ AveragedMeanSquareDensityAt (fun n : ℕ => ((μ n : ℤ) : ℝ) ^ (2 : ℕ))
          squarefreeDensity id hh
      ∧ ∀ p : ℕ, p.Prime → AveragedMeanSquareDensityAt (coprimeSquarefreeWeight p)
          (squarefreeDensity * (p : ℝ) / ((p : ℝ) + 1))
          (fun x => x / (p : ℝ) ^ (2 : ℕ)) (fun x => hh x / (p : ℝ)) := by
  refine ⟨averagedMeanSquare_of_maximal hhtop
      (maximalWindowMeanSquare_of_firstMoment abs_moebius_real_le_one hhtop
        (maximalWindowFirstMoment_moebius_long_window hhtop hlarge)),
    averagedMeanSquareDensityAt_of_maximal squarefreeDensity_nonneg' tendsto_id hhtop
      (maximalWindowDevMeanSquareAt_of_long tendsto_id hhtop hlarge (K := 6) (by norm_num)
        (fun y H hy hyH => maxWindowDevSq_moebius_sq_le_long hy hyH)), ?_⟩
  intro p hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hpsq : (0 : ℝ) < (p : ℝ) ^ (2 : ℕ) := by positivity
  refine averagedMeanSquareDensityAt_of_maximal (coprime_block_density_nonneg hp)
    (tendsto_id.atTop_div_const hpsq) (hhtop.atTop_div_const hp0) ?_
  refine maximalWindowDevMeanSquareAt_of_long (tendsto_id.atTop_div_const hpsq)
    (hhtop.atTop_div_const hp0) ?_ (K := 8) (by norm_num)
    (fun y H hy hyH => maxWindowDevSq_coprime_le_long hp hy hyH)
  filter_upwards [hlarge, eventually_ge_atTop (0 : ℝ)] with x hx hx0
  rw [sqrt_div_sq hx0 hp.pos]
  exact div_le_div_of_nonneg_right hx hp0.le

/-- **The card's Theorem `(3)` at long windows.**  When the window length is at least `√x`, every
short-interval input follows from the prime number theorem and the square-divisor count. -/
theorem route_e_sign_density_long_windows {hh : ℝ → ℝ} {s : ℤ} (hs : s = 1 ∨ s = -1)
    (hgrow : Tendsto (fun x => hh x / Real.log (Real.log (3 * x))) atTop atTop)
    (hlarge : ∀ᶠ x in atTop, Real.sqrt x ≤ hh x) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in atTop,
      squarefreeDensity ^ (2 : ℕ) / 2
          - squarefreeDensity ^ (2 : ℕ) * RHTower.coprimeSharedPrimeDensity - ε
        ≤ coprimeSignClassCount x (hh x) s / (hh x * Real.sqrt x * Real.log 2) := by
  obtain ⟨h1, h2, h3⟩ := routeE_longWindow_inputs (tendsto_of_growth hgrow) hlarge
  exact route_e_sign_density_of_meanSquare hs hgrow h1 h2 h3 hε

/-- **Both sign classes are eventually nonempty at long windows.** -/
theorem route_e_signClass_nonempty_long_windows {hh : ℝ → ℝ} {s : ℤ} (hs : s = 1 ∨ s = -1)
    (hgrow : Tendsto (fun x => hh x / Real.log (Real.log (3 * x))) atTop atTop)
    (hlarge : ∀ᶠ x in atTop, Real.sqrt x ≤ hh x) :
    ∀ᶠ x in atTop, (coprimeSignClass x (hh x) s).Nonempty := by
  obtain ⟨h1, h2, h3⟩ := routeE_longWindow_inputs (tendsto_of_growth hgrow) hlarge
  exact route_e_signClass_nonempty_of_meanSquare hs hgrow h1 h2 h3

end

end RHTower.Sieve
