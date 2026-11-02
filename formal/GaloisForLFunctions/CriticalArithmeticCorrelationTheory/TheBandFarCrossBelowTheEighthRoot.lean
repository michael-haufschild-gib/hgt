import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheJetPoleComponentCancelsThePole
import GaloisForLFunctions.CompletedArithmeticForms.TheNearCollarCostsTheMeanLogarithmicMultiplier
import GaloisForLFunctions.RHTower.ZetaSymbolArchimedeanHorizon

/-!
# The band–far cross below the eighth root

For a band `u = Σ_{m ≤ R} a_m v_m ⊥ v₁` and `w ⊥ V_R`, split `u = a₁v₁ + ũ`. The cross
`⟨W u, w⟩` decomposes (`band_far_cross_eq`) into

* the pole mode `a₁⟨r₁, w⟩`, `r₁ = W v₁ − E₁v₁` its residual;
* the prime channel on `ũ`;
* the coherent pole pair `P⟨Πũ, w⟩ + J₁⟨K₂ᵦ v₁, w⟩` (exact pole plus the jet's pole component,
  `TheJetPoleComponentCancelsThePole`);
* the center collar `α⟨C ũ, w⟩`, sharp at `O(max m/φ(m))/log N` (`collar_reducedBand_sq_le`, via
  the near multiplier `M_D`);
* the separated channel, the near remainder `(Overlap − Down)ũ − K₂ᵦ v_jet(ũ)`, and the reduced
  jet `K₂ᵦ v_jet'` (`TheReducedDivisorJetCostsItsDivisorMean`, with `Sg = (max m/φ(m))²`);
* the upward channel, split into prefix rows `n ≤ M` (corpus `O(c²(1 + log c))` bound) and top
  rows `n > M`, where the window `kn ≈ j ≤ N` forces `k ≤ 2N/M`
  (`exists_upwardPrimeVector_top_sq_le`: `O(c²(N/M)(1 + log c)/log N)`).

`exists_band_far_cross_le_channels` pays each channel by a free reserve parameter. With
`M = N/L_c` and `c ≤ (log N)^α`, every channel costs `c^{8+o(1)}/log N` or less per unit
band reserve against the far reserves `k₁P` and `(log N/c⁷)S`, i.e. it closes for `α < 1/8`.
The remainder of this file collects the totient-ratio bounds (`exists_div_totient_le_loglog`).
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Finset Filter Topology
open scoped RealInnerProductSpace Matrix

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open BezoutValuationIncidence RenormalizedArithmeticPotentialTheory CompletedArithmeticForms
  RenormalizedArithmeticPotentialTheory.CompletedShell SpacingScaleHarmonicAnalysis
  CriticalScaleArithmeticRigidity

/-! ### Totient ratios -/

/-- **Landau, uniformly.** `m/φ(m) ≤ K(1 + log(1 + log m))` for every `m ≥ 1`. -/
theorem exists_div_totient_le_loglog :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ m : ℕ, 1 ≤ m →
      (m : ℝ) / m.totient ≤ K * (1 + Real.log (1 + Real.log m)) := by
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.mp (RHTower.eventually_div_totient_le_landau one_pos)
  set E := Real.exp Real.eulerMascheroniConstant + 1
  have hE : 1 ≤ E := by have := Real.exp_pos Real.eulerMascheroniConstant; simp only [E]; linarith
  refine ⟨max E (n₀ + 2), le_trans hE (le_max_left _ _), ?_⟩
  intro m hm
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hφ : (1 : ℝ) ≤ m.totient := by exact_mod_cast Nat.totient_pos.mpr hm
  have hl0 : 0 ≤ Real.log (1 + Real.log m) :=
    Real.log_nonneg (by linarith [Real.log_natCast_nonneg m])
  by_cases h : n₀ ≤ m ∧ 3 ≤ m
  · have h1 := hn₀ m h.1
    have hlogm : 0 < Real.log m := Real.log_pos (by exact_mod_cast (by omega : 1 < m))
    have hll : Real.log (Real.log m) ≤ Real.log (1 + Real.log m) :=
      Real.log_le_log hlogm (by linarith)
    have hll0 : 0 ≤ Real.log (Real.log m) := by
      apply Real.log_nonneg
      have h3 : (3 : ℝ) ≤ m := by exact_mod_cast h.2
      have : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
      rw [← Real.log_exp 1]
      exact Real.log_le_log (Real.exp_pos 1) (by linarith)
    calc (m : ℝ) / m.totient ≤ E * Real.log (Real.log m) := h1
      _ ≤ max E (n₀ + 2) * (1 + Real.log (1 + Real.log m)) := by
          apply mul_le_mul (le_max_left _ _) (by linarith) hll0 (by positivity)
  · have hmle : (m : ℝ) ≤ n₀ + 2 := by
      push Not at h
      by_cases h' : n₀ ≤ m
      · have := h h'; have : (m : ℝ) ≤ 2 := by exact_mod_cast (by omega : m ≤ 2)
        linarith [(Nat.cast_nonneg n₀ : (0 : ℝ) ≤ n₀)]
      · have : (m : ℝ) ≤ n₀ := by exact_mod_cast (by omega : m ≤ n₀)
        linarith
    calc (m : ℝ) / m.totient ≤ m := div_le_self hm0.le hφ
      _ ≤ max E (n₀ + 2) := hmle.trans (le_max_right _ _)
      _ ≤ max E (n₀ + 2) * (1 + Real.log (1 + Real.log m)) := by
          have : 0 ≤ max E (n₀ + 2) := le_trans (by linarith) (le_max_left _ _)
          nlinarith

/-- `σ(m)/φ(m) ≤ (m/φ(m))²`. -/
theorem sigma_div_totient_le_sq {m : ℕ} (hm : 1 ≤ m) :
    (ArithmeticFunction.sigma 1 m : ℝ) / m.totient ≤ ((m : ℝ) / m.totient) ^ 2 := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hφ : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr hm
  have h := RHTower.sigma_div_le_div_totient (n := m) (by omega)
  have e : (ArithmeticFunction.sigma 1 m : ℝ) / m.totient =
      ((ArithmeticFunction.sigma 1 m : ℝ) / m) * ((m : ℝ) / m.totient) := by
    field_simp
  rw [e, sq]
  exact mul_le_mul_of_nonneg_right h (by positivity)

/-! ### The center collar on a pole-free band -/

theorem sum_collarSourceWeight_le (D : ℕ) :
    (∑ i ∈ range (2 * D + 1), collarSourceWeight D i) ≤ D + 1 := by
  have h : ∀ i ∈ range (2 * D + 1), collarSourceWeight D i ≤ 1 / 2 := by
    intro i _
    unfold collarSourceWeight
    split_ifs with hi
    · norm_num
    · have hd : (1 : ℝ) ≤ Nat.dist i D := by
        have : 1 ≤ Nat.dist i D := by
          rcases lt_or_gt_of_ne hi with h | h
          · unfold Nat.dist; omega
          · unfold Nat.dist; omega
        exact_mod_cast this
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  calc _ ≤ ∑ i ∈ range (2 * D + 1), (1 / 2 : ℝ) := sum_le_sum h
    _ = (2 * D + 1 : ℕ) * (1 / 2 : ℝ) := by rw [sum_const, card_range, nsmul_eq_mul]
    _ ≤ D + 1 := by push_cast; linarith

theorem near_collar_error_le {R : ℕ} (b : ℕ → ℝ) :
    (∑ m ∈ Icc 1 R, |b m| * m * Real.sqrt m.totient) ^ 2 +
        2 * (R : ℝ) ^ 4 * (∑ m ∈ Icc 1 R, |b m| * Real.sqrt m.totient) ^ 2 ≤
      3 * (R : ℝ) ^ 7 * ∑ m ∈ Icc 1 R, b m ^ 2 := by
  have hsφ : ∀ m ∈ Icc 1 R, Real.sqrt m.totient ≤ R := by
    intro m hm
    have hmR : (m : ℝ) ≤ R := by exact_mod_cast (mem_Icc.mp hm).2
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (mem_Icc.mp hm).1
    have hφm : (m.totient : ℝ) ≤ m := by exact_mod_cast Nat.totient_le m
    have : Real.sqrt m.totient ≤ Real.sqrt m := Real.sqrt_le_sqrt hφm
    have : Real.sqrt (m : ℝ) ≤ m := by
      rw [Real.sqrt_le_left (by linarith)]; nlinarith
    linarith
  have hS := sq_sum_le_card_mul_sum_sq (s := Icc 1 R) (f := fun m => |b m|)
  simp only [Nat.card_Icc, Nat.add_sub_cancel, sq_abs] at hS
  have hS0 : 0 ≤ ∑ m ∈ Icc 1 R, |b m| := sum_nonneg fun _ _ => abs_nonneg _
  have h1 : (∑ m ∈ Icc 1 R, |b m| * m * Real.sqrt m.totient) ≤ (R : ℝ) ^ 2 * ∑ m ∈ Icc 1 R, |b m| := by
    rw [mul_sum]
    refine sum_le_sum fun m hm => ?_
    have hmR : (m : ℝ) ≤ R := by exact_mod_cast (mem_Icc.mp hm).2
    have := hsφ m hm
    have hb := abs_nonneg (b m)
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have : (m : ℝ) * Real.sqrt m.totient ≤ R * R := mul_le_mul hmR this (Real.sqrt_nonneg _) (by positivity)
    nlinarith
  have h2 : (∑ m ∈ Icc 1 R, |b m| * Real.sqrt m.totient) ≤ (R : ℝ) * ∑ m ∈ Icc 1 R, |b m| := by
    rw [mul_sum]
    refine sum_le_sum fun m hm => ?_
    have := hsφ m hm
    have hb := abs_nonneg (b m)
    nlinarith
  have h10 : 0 ≤ ∑ m ∈ Icc 1 R, |b m| * m * Real.sqrt m.totient :=
    sum_nonneg fun m _ => by positivity
  have h20 : 0 ≤ ∑ m ∈ Icc 1 R, |b m| * Real.sqrt m.totient := sum_nonneg fun m _ => by positivity
  have hB0 : 0 ≤ ∑ m ∈ Icc 1 R, b m ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg R
  have e1 := pow_le_pow_left₀ h10 h1 2
  have e2 := pow_le_pow_left₀ h20 h2 2
  rw [mul_pow] at e1 e2
  have hR1 : (R : ℝ) ^ 5 ≤ (R : ℝ) ^ 7 ∨ R = 0 := by
    rcases Nat.eq_zero_or_pos R with h | h
    · right; exact h
    · left; have : (1 : ℝ) ≤ R := by exact_mod_cast h
      exact pow_le_pow_right₀ this (by norm_num)
  rcases hR1 with hR1 | hR0'
  · have f1 : ((R : ℝ) ^ 2) ^ 2 * (∑ m ∈ Icc 1 R, |b m|) ^ 2 ≤ (R : ℝ) ^ 5 * ∑ m ∈ Icc 1 R, b m ^ 2 := by
      have := mul_le_mul_of_nonneg_left hS (by positivity : (0 : ℝ) ≤ (R : ℝ) ^ 4)
      nlinarith
    have f2 : 2 * (R : ℝ) ^ 4 * ((R : ℝ) ^ 2 * (∑ m ∈ Icc 1 R, |b m|) ^ 2) ≤
        2 * (R : ℝ) ^ 7 * ∑ m ∈ Icc 1 R, b m ^ 2 := by
      have := mul_le_mul_of_nonneg_left hS (by positivity : (0 : ℝ) ≤ 2 * (R : ℝ) ^ 6)
      nlinarith
    have f3 := mul_le_mul_of_nonneg_left e2 (by positivity : (0 : ℝ) ≤ 2 * (R : ℝ) ^ 4)
    have f4 := mul_le_mul_of_nonneg_right hR1 hB0
    nlinarith
  · subst hR0'; simp

/-- **The center collar on a pole-free band.** For `u = Σ_{m ≤ R} a_m v_m` with pole-free part
`ũ` and `Sg₁ ≥ m/φ(m)` on `[2, R]`, the sharp near collar gives
`‖C ũ‖² ≤ (24 + 780 Sg₁ + 72 R^{15}/N)/log N · ‖u‖²`, `C` the collar kernel. -/
theorem collar_reducedBand_sq_le {R N : ℕ} (hR : 2 ≤ R) (hRN6 : R ^ 6 ≤ N)
    (hlog : 18 * (1 + Real.log R) ≤ Real.log N) (a : ℕ → ℝ) {Sg₁ : ℝ} (hSg0 : 0 ≤ Sg₁)
    (hSg : ∀ m ∈ Icc 2 R, (m : ℝ) / m.totient ≤ Sg₁) :
    ‖Matrix.toEuclideanLin (horizonKernelMatrix (collarKernel N) N)
        (∑ m ∈ Icc 1 R, (if m = 1 then 0 else a m) • normalizedRamanujanHorizonVector m N)‖ ^ 2 ≤
      (24 + 780 * Sg₁ + 72 * (R : ℝ) ^ 15 / N) / Real.log N *
        ‖∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 := by
  have hRN4 : R ^ 4 ≤ N := (Nat.pow_le_pow_right (by omega : 0 < R) (by omega : 4 ≤ 6)).trans hRN6
  have hRN2 : R * R ≤ N := by
    have : R ^ 2 ≤ R ^ 6 := Nat.pow_le_pow_right (by omega : 0 < R) (by omega : 2 ≤ 6)
    simpa only [sq] using this.trans hRN6
  have hN1 : 1 ≤ N := by have : 4 ≤ R * R := Nat.mul_le_mul hR hR; omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hL : 0 < Real.log N := by have := Real.log_natCast_nonneg R; linarith
  set aT : ℕ → ℝ := fun m => if m = 1 then 0 else a m with haT
  set uT := ∑ m ∈ Icc 1 R, aT m • normalizedRamanujanHorizonVector m N
  set u := ∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N
  have haT1 : aT 1 = 0 := by simp [haT]
  have ha_sq : (∑ m ∈ Icc 1 R, aT m ^ 2) ≤ 2 * ‖u‖ ^ 2 := by
    have hle : (∑ m ∈ Icc 1 R, aT m ^ 2) ≤ ∑ m ∈ Icc 1 R, a m ^ 2 :=
      sum_le_sum fun m _ => by simp only [haT]; split_ifs <;> simp [sq_nonneg]
    have hr := (half_and_three_halves_riesz_of_log_le hR hRN2 hlog a).1
    linarith
  have huT_mem : uT ∈ conductorSubspace R N :=
    sum_normalizedRamanujanHorizonVector_mem_conductorSubspace R N aT
  have huT_sq : ‖uT‖ ^ 2 ≤ 3 * ‖u‖ ^ 2 := by
    have hr := (half_and_three_halves_riesz_of_log_le hR hRN2 hlog aT).2
    linarith
  have hlin : (∑ j ∈ Icc 1 N, ((j : ℝ) / N) * primeHorizonExtension uT j ^ 2) ≤
      16 / Real.log N * ‖u‖ ^ 2 := by
    have hm := sum_linear_moment_sq_le_four_div_log hR hRN4 hlog huT_mem
    rw [div_mul_eq_mul_div, le_div_iff₀' hL]
    nlinarith [sq_nonneg ‖u‖]
  have h3 : ∀ x₁ x₂ x₃ : ℝ, (x₁ + x₂ + x₃) ^ 2 ≤ 3 * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2) :=
    fun x₁ x₂ x₃ => by
      nlinarith only [sq_nonneg (x₁ - x₂), sq_nonneg (x₁ - x₃), sq_nonneg (x₂ - x₃)]
  have hpt : ∀ n ∈ Icc 1 N,
      (∑ j ∈ Icc 1 N, collarKernel N n j * primeHorizonExtension uT j) ^ 2 ≤
        3 * (collarRowSumHalf R N aT n ^ 2 + collarRowNear R N aT n ^ 2 +
          collarRowFar R N aT n ^ 2) := by
    intro n hn
    rw [collarRow_eq_sum_three hR hN1 hL aT hn]
    exact h3 _ _ _
  have hsumHalf := sum_collarRowSumHalf_sq_le hN1 aT hlin
  have hfar := sum_collarRowFar_sq_le hR hN1 hL aT haT1 (norm_nonneg u) ha_sq
  have hnear := sum_collarRowNear_sq_le_sharp (by omega : 1 ≤ R) hN1 hL aT haT1
  -- the sharp near collar
  have hmean : (∑ m ∈ Icc 1 R, aT m ^ 2 * ((m : ℝ) / m.totient)) ≤ Sg₁ * (2 * ‖u‖ ^ 2) := by
    have : (∑ m ∈ Icc 1 R, aT m ^ 2 * ((m : ℝ) / m.totient)) ≤ ∑ m ∈ Icc 1 R, aT m ^ 2 * Sg₁ := by
      refine sum_le_sum fun m hm => ?_
      by_cases h1 : m = 1
      · subst h1; simp [haT1]
      · apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        exact hSg m (mem_Icc.mpr ⟨by have := (mem_Icc.mp hm).1; omega, (mem_Icc.mp hm).2⟩)
    rw [← sum_mul] at this
    nlinarith
  have hH := sum_collarSourceWeight_le (R ^ 4)
  have hH0 : 0 ≤ ∑ i ∈ range (2 * R ^ 4 + 1), collarSourceWeight (R ^ 4) i :=
    sum_nonneg fun i _ => by unfold collarSourceWeight; split_ifs <;> positivity
  have hH2 : (∑ i ∈ range (2 * R ^ 4 + 1), collarSourceWeight (R ^ 4) i) ^ 2 ≤ 4 * (R : ℝ) ^ 8 := by
    have hR1 : (1 : ℝ) ≤ (R : ℝ) ^ 4 := one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ R))
    have : (∑ i ∈ range (2 * R ^ 4 + 1), collarSourceWeight (R ^ 4) i) ≤ 2 * (R : ℝ) ^ 4 := by
      push_cast at hH; linarith
    have := pow_le_pow_left₀ hH0 this 2
    nlinarith
  have herr := near_collar_error_le (R := R) aT
  have hnear' : (∑ n ∈ Icc 1 N, collarRowNear R N aT n ^ 2) ≤
      (260 * Sg₁ + 24 * (R : ℝ) ^ 15 / N) / Real.log N * ‖u‖ ^ 2 := by
    refine hnear.trans ?_
    have t1 : 130 / Real.log N * (∑ m ∈ Icc 1 R, aT m ^ 2 * ((m : ℝ) / m.totient)) ≤
        260 * Sg₁ / Real.log N * ‖u‖ ^ 2 := by
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hL]
      nlinarith
    have t2 : (∑ i ∈ range (2 * R ^ 4 + 1), collarSourceWeight (R ^ 4) i) ^ 2 /
          ((N : ℝ) * Real.log N) *
          ((∑ m ∈ Icc 1 R, |aT m| * m * Real.sqrt m.totient) ^ 2 +
            2 * (R : ℝ) ^ 4 * (∑ m ∈ Icc 1 R, |aT m| * Real.sqrt m.totient) ^ 2) ≤
        24 * (R : ℝ) ^ 15 / N / Real.log N * ‖u‖ ^ 2 := by
      have hE0 : 0 ≤ (∑ m ∈ Icc 1 R, |aT m| * m * Real.sqrt m.totient) ^ 2 +
          2 * (R : ℝ) ^ 4 * (∑ m ∈ Icc 1 R, |aT m| * Real.sqrt m.totient) ^ 2 := by positivity
      calc _ ≤ 4 * (R : ℝ) ^ 8 / ((N : ℝ) * Real.log N) *
            (3 * (R : ℝ) ^ 7 * (2 * ‖u‖ ^ 2)) := by
            apply mul_le_mul (div_le_div_of_nonneg_right hH2 (by positivity)) _ hE0 (by positivity)
            exact herr.trans (mul_le_mul_of_nonneg_left ha_sq (by positivity))
        _ = 24 * (R : ℝ) ^ 15 / N / Real.log N * ‖u‖ ^ 2 := by field_simp; ring
    have e : (260 * Sg₁ + 24 * (R : ℝ) ^ 15 / N) / Real.log N * ‖u‖ ^ 2 =
        260 * Sg₁ / Real.log N * ‖u‖ ^ 2 + 24 * (R : ℝ) ^ 15 / N / Real.log N * ‖u‖ ^ 2 := by
      ring
    rw [e]; linarith
  rw [← horizonProfileVector_extension uT, horizonKernelMatrix_profile_norm_sq]
  calc _ ≤ 3 * ((∑ n ∈ Icc 1 N, collarRowSumHalf R N aT n ^ 2) +
          (∑ n ∈ Icc 1 N, collarRowNear R N aT n ^ 2) +
          (∑ n ∈ Icc 1 N, collarRowFar R N aT n ^ 2)) := by
        refine (sum_le_sum hpt).trans_eq ?_
        rw [← mul_sum, sum_add_distrib, sum_add_distrib]
    _ ≤ 3 * (4 / Real.log N * ‖u‖ ^ 2 +
          (260 * Sg₁ + 24 * (R : ℝ) ^ 15 / N) / Real.log N * ‖u‖ ^ 2 +
          4 / Real.log N * ‖u‖ ^ 2) := by linarith
    _ = _ := by ring

/-! ### The upward channel on the top rows -/

/-- At most `2d/k + 1` integers `n` have `|kn − m| ≤ d`. -/
theorem card_filter_abs_mul_sub_le (S : Finset ℕ) {k : ℕ} (hk : 1 ≤ k) {m d : ℝ} (hm : 0 ≤ m)
    (hd : 0 ≤ d) :
    ((S.filter fun n : ℕ => |(k : ℝ) * n - m| ≤ d).card : ℝ) ≤ 2 * d / k + 1 := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  set a := ⌈(m - d) / k⌉₊
  set b := ⌊(m + d) / k⌋₊
  have hsub : (S.filter fun n : ℕ => |(k : ℝ) * n - m| ≤ d) ⊆ Icc a b := by
    intro n hn
    obtain ⟨-, h⟩ := mem_filter.mp hn
    rw [abs_le] at h
    refine mem_Icc.mpr ⟨Nat.ceil_le.mpr ?_, Nat.le_floor ?_⟩
    · rw [div_le_iff₀ hk0]; linarith
    · rw [le_div_iff₀ hk0]; linarith
  refine (Nat.cast_le.mpr (card_le_card hsub)).trans ?_
  rw [Nat.card_Icc]
  have hb : (b : ℝ) ≤ (m + d) / k := Nat.floor_le (by positivity)
  have ha : (m - d) / k ≤ (a : ℝ) := Nat.le_ceil _
  have hsplit : (2 * d / k + 1 : ℝ) = (m + d) / k + 1 - (m - d) / k := by field_simp; ring
  by_cases hab : a ≤ b + 1
  · rw [Nat.cast_sub hab]; push_cast; linarith
  · rw [Nat.sub_eq_zero_of_le (by omega)]; push_cast; positivity

/-- **The upward column on the top rows.** Restricted to rows `n > M`, the upward window at `m`
has total weight `≤ 7e^{w/2}(2d + 1)(m + d)/M`, `d = m(e^w − 1)`. -/
theorem down_row_top_le {w : ℝ} (hw : 0 ≤ w) {m N M : ℕ} (hm : 1 ≤ m) (hM : 1 ≤ M) (K : ℕ) :
    ∑ k ∈ range K, _root_.RHTower.vonMangoldtAtom k * ∑ n ∈ Icc 1 N,
        (if M < n then Real.sqrt ((m : ℝ) / n) * upInd w k n m else 0) ≤
      7 * Real.exp (w / 2) * (2 * (m * (Real.exp w - 1)) + 1) *
        ((m + m * (Real.exp w - 1)) / M) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hew : 0 ≤ Real.exp w - 1 := by linarith [Real.add_one_le_exp w]
  set d := (m : ℝ) * (Real.exp w - 1) with hd
  have hd0 : 0 ≤ d := by positivity
  set Y := ((m : ℝ) + d) / M with hY
  have hY0 : 0 ≤ Y := by positivity
  have he0 : 0 < Real.exp (w / 2) := Real.exp_pos _
  -- one order at a time
  have hk : ∀ k ∈ range K, _root_.RHTower.vonMangoldtAtom k * ∑ n ∈ Icc 1 N,
      (if M < n then Real.sqrt ((m : ℝ) / n) * upInd w k n m else 0) ≤
      Real.exp (w / 2) * (2 * d + 1) *
        (if (k : ℝ) ≤ Y then ArithmeticFunction.vonMangoldt k else 0) := by
    intro k _
    rcases lt_or_ge k 2 with hk2 | hk2
    · rw [vonMangoldtAtom_eq_zero_of_lt_two hk2, zero_mul]
      have : 0 ≤ (if (k : ℝ) ≤ Y then ArithmeticFunction.vonMangoldt k else 0) := by
        split_ifs <;> [exact ArithmeticFunction.vonMangoldt_nonneg; exact le_rfl]
      positivity
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
    have hsk : 0 < Real.sqrt k := Real.sqrt_pos.mpr hk0
    have hΛ := ArithmeticFunction.vonMangoldt_nonneg (n := k)
    -- each term is at most `e^{w/2} Λ(k)` times the window indicator
    have hterm : ∀ n ∈ Icc 1 N, _root_.RHTower.vonMangoldtAtom k *
        (if M < n then Real.sqrt ((m : ℝ) / n) * upInd w k n m else 0) ≤
        Real.exp (w / 2) * ArithmeticFunction.vonMangoldt k *
          (if |(k : ℝ) * n - m| ≤ d ∧ (k : ℝ) ≤ Y then 1 else 0) := by
      intro n hn
      have hn1 := (mem_Icc.mp hn).1
      by_cases hMn : M < n
      · rw [if_pos hMn]
        unfold upInd upWin
        by_cases h1 : m ≠ k * n ∧ |Real.log k - (Real.log m - Real.log n)| ≤ w
        · obtain ⟨hb1, hb2⟩ := downWin_bounds (by omega) hm hn1 h1.2
          have hkn : |(k : ℝ) * n - m| ≤ d := by push_cast at hb2; exact hb2
          have hkY : (k : ℝ) ≤ Y := by
            have hMn' : (M : ℝ) ≤ n := by exact_mod_cast hMn.le
            have h2 : (k : ℝ) * n ≤ m + d := by linarith [(abs_le.mp hkn).2]
            rw [hY, le_div_iff₀ hM0]
            nlinarith
          rw [if_pos h1, if_pos ⟨hkn, hkY⟩, mul_one, mul_one, vonMangoldtAtom_eq hk2]
          calc ArithmeticFunction.vonMangoldt k / Real.sqrt k * Real.sqrt ((m : ℝ) / n)
              ≤ ArithmeticFunction.vonMangoldt k / Real.sqrt k * (Real.exp (w / 2) * Real.sqrt k) :=
                mul_le_mul_of_nonneg_left hb1 (by positivity)
            _ = Real.exp (w / 2) * ArithmeticFunction.vonMangoldt k := by field_simp
        · rw [if_neg h1, mul_zero, mul_zero]
          split_ifs <;> positivity
      · rw [if_neg hMn, mul_zero]
        split_ifs <;> positivity
    rw [mul_sum]
    refine (sum_le_sum hterm).trans ?_
    rw [← mul_sum]
    by_cases hkY : (k : ℝ) ≤ Y
    · rw [if_pos hkY]
      have hcount : (∑ n ∈ Icc 1 N, (if |(k : ℝ) * n - m| ≤ d ∧ (k : ℝ) ≤ Y then (1 : ℝ) else 0)) ≤
          2 * d + 1 := by
        rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
        have hfil : ((Icc 1 N).filter (fun n : ℕ => |(k : ℝ) * n - m| ≤ d ∧ (k : ℝ) ≤ Y)) =
            ((Icc 1 N).filter (fun n : ℕ => |(k : ℝ) * n - m| ≤ d)) := by
          ext n; simp only [mem_filter]; tauto
        rw [hfil]
        refine (card_filter_abs_mul_sub_le (Icc 1 N) (show 1 ≤ k by omega) hm0.le hd0).trans ?_
        have : 2 * d / k ≤ 2 * d := div_le_self (by positivity) hk1
        linarith
      calc Real.exp (w / 2) * ArithmeticFunction.vonMangoldt k *
            (∑ n ∈ Icc 1 N, (if |(k : ℝ) * n - m| ≤ d ∧ (k : ℝ) ≤ Y then (1 : ℝ) else 0))
          ≤ Real.exp (w / 2) * ArithmeticFunction.vonMangoldt k * (2 * d + 1) :=
            mul_le_mul_of_nonneg_left hcount (by positivity)
        _ = _ := by ring
    · rw [if_neg hkY, mul_zero]
      have : (∑ n ∈ Icc 1 N, (if |(k : ℝ) * n - m| ≤ d ∧ (k : ℝ) ≤ Y then (1 : ℝ) else 0)) = 0 :=
        sum_eq_zero fun n _ => if_neg (fun h => hkY h.2)
      rw [this, mul_zero]
  refine (sum_le_sum hk).trans ?_
  rw [← mul_sum]
  have hsumΛ : (∑ k ∈ range K, (if (k : ℝ) ≤ Y then ArithmeticFunction.vonMangoldt k else 0)) ≤
      7 * Y := by
    rw [← sum_filter]
    have hsub : (range K).filter (fun k : ℕ => (k : ℝ) ≤ Y) ⊆ insert 0 (Icc 1 ⌊Y⌋₊) := by
      intro k hk
      obtain ⟨-, hkY⟩ := mem_filter.mp hk
      rcases Nat.eq_zero_or_pos k with h | h
      · exact mem_insert.mpr (Or.inl h)
      · exact mem_insert.mpr (Or.inr (mem_Icc.mpr ⟨h, Nat.le_floor hkY⟩))
    calc _ ≤ ∑ k ∈ insert 0 (Icc 1 ⌊Y⌋₊), (ArithmeticFunction.vonMangoldt k : ℝ) :=
          sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg
      _ = ∑ k ∈ Icc 1 ⌊Y⌋₊, (ArithmeticFunction.vonMangoldt k : ℝ) := by
          rw [sum_insert (by simp)]; simp
      _ ≤ 7 * ⌊Y⌋₊ := RHTower.sum_vonMangoldt_Icc_le_seven _
      _ ≤ 7 * Y := by have := Nat.floor_le hY0; linarith
  calc _ ≤ Real.exp (w / 2) * (2 * d + 1) * (7 * Y) :=
        mul_le_mul_of_nonneg_left hsumΛ (by positivity)
    _ = _ := by ring

/-- **The upward channel on the top rows.** On rows `n > M` the upward vector of a band
`u ∈ V_R` has `Σ_{n > M} (Up u)_n² ≤ C c² (N/M)(1 + log c)/log N · ‖u‖²`. -/
theorem exists_upwardPrimeVector_top_sq_le {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {R N M : ℕ} {c : ℝ},
        2 ≤ R → 18 * (1 + Real.log R) ≤ Real.log N →
        1 ≤ c → c / N ≤ 1 / 3 →
        ((R * R : ℕ) + 1 : ℝ) * (c * Real.exp 1 + 1) ≤ N → 1 ≤ M →
      ∀ {u : EuclideanSpace ℝ (PrimeHorizonIndex N)},
        u ∈ conductorSubspace R N →
        (∑ n ∈ Icc 1 N, if M < n then
            primeHorizonExtension (upwardPrimeVector φ c N u) n ^ 2 else 0) ≤
          C * c ^ 2 * ((N : ℝ) / M) * (1 + Real.log c) / Real.log N * ‖u‖ ^ 2 := by
  classical
  let A_up : ℝ := 2 * (Real.log 4 + 4) * Real.exp (3 / 2) * Real.exp 1
  have hlog4_pos : 0 < Real.log 4 + 4 := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num); linarith
  have hA_up_pos : 0 < A_up := by dsimp only [A_up]; positivity
  refine ⟨16 * (42 * Real.exp (3 / 2) * A_up), by positivity, ?_⟩
  intro R N M c hR hlog hc1 hw1 hRNT hM1 u hu
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hw_le1 : c / N ≤ 1 := hw1.trans (by norm_num)
  have hN0 : (0 : ℝ) < N := by
    have : (0 : ℝ) < ((R * R : ℕ) + 1 : ℝ) * (c * Real.exp 1 + 1) := by positivity
    linarith only [this, hRNT]
  have hN1 : 1 ≤ N := by
    have : (1 : ℝ) ≤ ((R * R : ℕ) + 1 : ℝ) * (c * Real.exp 1 + 1) := by
      have h1 : (0 : ℝ) ≤ c * Real.exp 1 := by positivity
      have h2 : (0 : ℝ) ≤ (R * R : ℕ) := by positivity
      nlinarith only [h1, h2]
    exact_mod_cast this.trans hRNT
  have hL1 : 1 ≤ Real.log N := by have := Real.log_natCast_nonneg R; linarith only [hlog, this]
  have hL0 : 0 < Real.log N := zero_lt_one.trans_le hL1
  let w := c / N
  have hw0 : 0 < w := div_pos hc0 hN0
  obtain ⟨hg, hgsupp, _⟩ := atomDilate_facts hφ hsupp hw0
  let g := atomDilate φ w
  let G0 := ∫ t, g t ^ 2
  have hG0 : 0 < G0 := by
    dsimp only [G0, g]; rw [integral_atomDilate_sq hw0]; exact mul_pos hw0 hM
  have hgc : HasCompactSupport g := HasCompactSupport.intro isCompact_Icc hgsupp
  let K := lagRange (Real.log N + w + 1)
  let T := c * Real.exp 1 + 1
  have hT1 : 1 ≤ T := by
    have h0 : 0 ≤ c * Real.exp 1 := by positivity
    dsimp only [T]; linarith only [h0]
  let uTop : ℕ → ℝ := fun j => if (N : ℝ) / j < T then primeHorizonExtension u j else 0
  let K_up : ℕ → ℕ → ℝ := fun n j =>
    (∑ k ∈ range K, _root_.RHTower.vonMangoldtAtom k *
      (if j = k * n then 0 else bumpCorr g (Real.log k - (Real.log j - Real.log n)))) / G0
  let U : ℕ → ℕ → ℝ := fun n j =>
    ∑ k ∈ range K, _root_.RHTower.vonMangoldtAtom k * upInd w k n j
  have hrow_eq : ∀ n ∈ Icc 1 N,
      primeHorizonExtension (upwardPrimeVector φ c N u) n =
        ∑ j ∈ Icc 1 N, K_up n j * uTop j := by
    intro n hn
    rw [primeHorizonExtension_coe _ ⟨n, hn⟩]
    change upwardPrimeRow g N (primeHorizonExtension u) n / G0 = _
    rw [upwardPrimeRow_eq_sum hgsupp hw0.le hn (primeHorizonExtension u)]
    have hcomm :
        (∑ k ∈ range K, _root_.RHTower.vonMangoldtAtom k *
          ∑ j ∈ Icc 1 N, primeHorizonExtension u j *
            (if j = k * n then 0 else bumpCorr g (Real.log k - (Real.log j - Real.log n)))) / G0 =
        ∑ j ∈ Icc 1 N, K_up n j * primeHorizonExtension u j := by
      simp_rw [mul_sum]
      rw [sum_comm, sum_div]
      refine sum_congr rfl fun j _ => ?_
      dsimp only [K_up]
      rw [div_mul_eq_mul_div, sum_mul]
      congr 1
      exact sum_congr rfl fun k _ => by ring
    rw [hcomm]
    refine sum_congr rfl fun j hj => ?_
    dsimp only [uTop]
    split_ifs with hlt
    · rfl
    · rw [mul_zero]
      have hKup0 : K_up n j = 0 := by
        dsimp only [K_up]
        rw [sum_eq_zero, zero_div]
        intro k _
        rcases lt_or_ge k 2 with hk2 | hk2
        · rw [vonMangoldtAtom_eq_zero_of_lt_two hk2, zero_mul]
        · split_ifs with hjn
          · rw [mul_zero]
          · by_cases hbc : bumpCorr g (Real.log k - (Real.log j - Real.log n)) = 0
            · rw [hbc, mul_zero]
            · exfalso
              have hk1 : 1 ≤ k := by omega
              have hn1 : 1 ≤ n := (mem_Icc.mp hn).1
              have hj1 : 1 ≤ j := (mem_Icc.mp hj).1
              have hkn1 : 1 ≤ k * n := Nat.mul_pos hk1 hn1
              have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
              have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
              have hj0 : (0 : ℝ) < j := by exact_mod_cast hj1
              have hgap : |Real.log k - (Real.log j - Real.log n)| ≤ w := by
                by_contra hgt
                exact hbc (bumpCorr_eq_zero hgsupp (lt_of_not_ge hgt))
              have hlog_eq : Real.log j - Real.log (k * n : ℕ) =
                  -(Real.log k - (Real.log j - Real.log n)) := by
                rw [Nat.cast_mul, Real.log_mul hk0.ne' hn0.ne']; ring
              have hlog_kn : |Real.log j - Real.log (k * n : ℕ)| ≤ c / N := by
                rwa [hlog_eq, abs_neg]
              have hsep := (logWindow_integer_separation_small_width hc0 hN1 hkn1 hj1
                (Ne.symm hjn) hlog_kn hw_le1).2
              have hdiv : (N : ℝ) / j ≤ c * Real.exp 1 := (div_le_iff₀ hj0).mpr hsep
              exact hlt (by dsimp only [T]; linarith only [hdiv])
      rw [hKup0, zero_mul]
  have hKU : ∀ n ∈ Icc 1 N, ∀ j ∈ Icc 1 N, |K_up n j| ≤ U n j := by
    intro n _ j _
    dsimp only [K_up, U]
    rw [abs_div, abs_of_pos hG0, div_le_iff₀ hG0, sum_mul]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k _ => ?_)
    rw [abs_mul, abs_of_nonneg (vonMangoldtAtom_nonneg' k), mul_assoc]
    exact mul_le_mul_of_nonneg_left
      ((abs_nonRatio_term_le hg.continuous hgc hgsupp k n j).trans_eq (mul_comm G0 _))
      (vonMangoldtAtom_nonneg' k)
  have hew : Real.exp w - 1 ≤ (c / N) * Real.exp 1 := by
    calc
      Real.exp w - 1 ≤ w * Real.exp w := exp_sub_one_le_mul_exp
      _ ≤ (c / N) * Real.exp 1 :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hw_le1) hw0.le
  have hU_row : ∀ n ∈ Icc 1 N,
      (∑ j ∈ Icc 1 N, U n j * (1 / Real.sqrt j)) ≤ A_up * c / Real.sqrt n := by
    intro n hn
    have hn1 : 1 ≤ n := (mem_Icc.mp hn).1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
    have heq : (∑ j ∈ Icc 1 N, U n j * (1 / Real.sqrt j)) =
        (1 / Real.sqrt n) * ∑ k ∈ range K, _root_.RHTower.vonMangoldtAtom k *
          ∑ j ∈ Icc 1 N, Real.sqrt ((n : ℝ) / j) * upInd w k n j := by
      dsimp only [U]
      simp_rw [sum_mul]
      rw [sum_comm, mul_sum]
      refine sum_congr rfl fun k _ => ?_
      rw [← mul_assoc, mul_comm (1 / Real.sqrt n), mul_assoc, mul_sum, mul_sum]
      refine sum_congr rfl fun j hj => ?_
      have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Icc.mp hj).1
      rw [Real.sqrt_div hn0.le]
      field_simp [hsn.ne', (Real.sqrt_pos.mpr hj0).ne']
    rw [heq, div_eq_mul_one_div (A_up * c), mul_comm (A_up * c)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hup := up_row_le (N := N) hw0.le hn1 K
    have hexp32 : Real.exp (3 * w / 2) ≤ Real.exp (3 / 2) :=
      Real.exp_le_exp.mpr (by dsimp only [w]; linarith only [hw_le1])
    have hewN : (Real.exp w - 1) * N ≤ c * Real.exp 1 := by
      calc
        (Real.exp w - 1) * N ≤ ((c / N) * Real.exp 1) * N :=
          mul_le_mul_of_nonneg_right hew hN0.le
        _ = c * Real.exp 1 := by field_simp [hN0.ne']
    calc
      _ ≤ 2 * (Real.log 4 + 4) * Real.exp (3 * w / 2) * ((Real.exp w - 1) * N) := by
        linarith only [hup, (by ring :
          2 * (Real.log 4 + 4) * Real.exp (3 * w / 2) * (Real.exp w - 1) * N =
            2 * (Real.log 4 + 4) * Real.exp (3 * w / 2) * ((Real.exp w - 1) * N))]
      _ ≤ 2 * (Real.log 4 + 4) * Real.exp (3 / 2) * (c * Real.exp 1) :=
        mul_le_mul
          (mul_le_mul_of_nonneg_left hexp32 (by positivity))
          hewN (mul_nonneg (by linarith [Real.add_one_le_exp w]) hN0.le) (by positivity)
      _ = A_up * c := by dsimp only [A_up]; ring
  have hU_col : ∀ j ∈ Icc 1 N,
      (∑ n ∈ Icc 1 N, (if M < n then U n j else 0) * ((A_up * c / Real.sqrt n) / (1 / Real.sqrt j))) ≤
        42 * Real.exp (3 / 2) * A_up * c ^ 2 * ((N : ℝ) / M) := by
    intro j hj
    have hj1 : 1 ≤ j := (mem_Icc.mp hj).1
    have hjN : (j : ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp hj).2
    have hj0 : (0 : ℝ) < j := by exact_mod_cast hj1
    have hsj : 0 < Real.sqrt j := Real.sqrt_pos.mpr hj0
    have hM0 : (0 : ℝ) < M := by exact_mod_cast hM1
    have hn_eq : ∀ n ∈ Icc 1 N,
        (if M < n then U n j else 0) * ((A_up * c / Real.sqrt n) / (1 / Real.sqrt j)) =
          (A_up * c) * ∑ k ∈ range K, _root_.RHTower.vonMangoldtAtom k *
            (if M < n then Real.sqrt ((j : ℝ) / n) * upInd w k n j else 0) := by
      intro n hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
      have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
      by_cases hMn : M < n
      · simp only [if_pos hMn]
        dsimp only [U]
        rw [Real.sqrt_div hj0.le, sum_mul, mul_sum]
        refine sum_congr rfl fun k _ => ?_
        field_simp
      · simp only [if_neg hMn, zero_mul, mul_zero, sum_const_zero]
    rw [sum_congr rfl hn_eq, ← mul_sum, sum_comm]
    have hswap : (∑ k ∈ range K, ∑ n ∈ Icc 1 N, _root_.RHTower.vonMangoldtAtom k *
        (if M < n then Real.sqrt ((j : ℝ) / n) * upInd w k n j else 0)) =
        ∑ k ∈ range K, _root_.RHTower.vonMangoldtAtom k *
          ∑ n ∈ Icc 1 N, (if M < n then Real.sqrt ((j : ℝ) / n) * upInd w k n j else 0) :=
      sum_congr rfl fun k _ => (mul_sum _ _ _).symm
    rw [hswap]
    have hcol := down_row_top_le (N := N) hw0.le hj1 hM1 K
    have hd : (j : ℝ) * (Real.exp w - 1) ≤ c * Real.exp 1 := by
      calc (j : ℝ) * (Real.exp w - 1) ≤ (N : ℝ) * ((c / N) * Real.exp 1) :=
            mul_le_mul hjN hew (by linarith [Real.add_one_le_exp w]) hN0.le
        _ = c * Real.exp 1 := by field_simp
    have hd0 : 0 ≤ (j : ℝ) * (Real.exp w - 1) := mul_nonneg hj0.le (by linarith [Real.add_one_le_exp w])
    have hce1 : 1 ≤ c * Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ); nlinarith
    have hceN : c * Real.exp 1 ≤ N := by
      have h2 : (0 : ℝ) ≤ (R * R : ℕ) := Nat.cast_nonneg _
      nlinarith [hRNT]
    have hexp12 : Real.exp (w / 2) ≤ Real.exp (1 / 2) :=
      Real.exp_le_exp.mpr (by dsimp only [w]; linarith only [hw_le1])
    have hb1 : 2 * ((j : ℝ) * (Real.exp w - 1)) + 1 ≤ 3 * (c * Real.exp 1) := by linarith
    have hb2 : ((j : ℝ) + (j : ℝ) * (Real.exp w - 1)) / M ≤ 2 * ((N : ℝ) / M) := by
      rw [div_le_iff₀ hM0, mul_assoc, div_mul_cancel₀ _ hM0.ne']; linarith
    have hbound : 7 * Real.exp (w / 2) * (2 * ((j : ℝ) * (Real.exp w - 1)) + 1) *
        (((j : ℝ) + (j : ℝ) * (Real.exp w - 1)) / M) ≤
        7 * Real.exp (1 / 2) * (3 * (c * Real.exp 1)) * (2 * ((N : ℝ) / M)) := by
      have hpos1 : 0 ≤ 2 * ((j : ℝ) * (Real.exp w - 1)) + 1 := by linarith
      have hpos2 : 0 ≤ ((j : ℝ) + (j : ℝ) * (Real.exp w - 1)) / M := by positivity
      apply mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hexp12 (by norm_num)) hb1 hpos1
        (by positivity)) hb2 hpos2 (by positivity)
    have he : Real.exp (1 / 2) * Real.exp 1 = Real.exp (3 / 2) := by
      rw [← Real.exp_add]; norm_num
    calc (A_up * c) * _ ≤ (A_up * c) * (7 * Real.exp (1 / 2) * (3 * (c * Real.exp 1)) *
          (2 * ((N : ℝ) / M))) :=
          mul_le_mul_of_nonneg_left (hcol.trans hbound) (by positivity)
      _ = 42 * (Real.exp (1 / 2) * Real.exp 1) * A_up * c ^ 2 * ((N : ℝ) / M) := by ring
      _ = _ := by rw [he]
  have hU_nonneg' : ∀ n ∈ Icc 1 N, ∀ j ∈ Icc 1 N, 0 ≤ (if M < n then U n j else 0) := by
    intro n _ j _
    split_ifs
    · exact sum_nonneg fun k _ => mul_nonneg (vonMangoldtAtom_nonneg' k)
        (by unfold upInd; split_ifs <;> norm_num)
    · exact le_rfl
  have hKU' : ∀ n ∈ Icc 1 N, ∀ j ∈ Icc 1 N,
      |(if M < n then K_up n j else 0)| ≤ (if M < n then U n j else 0) := by
    intro n hn j hj
    split_ifs
    · exact hKU n hn j hj
    · simp
  have hU_row' : ∀ n ∈ Icc 1 N,
      (∑ j ∈ Icc 1 N, (if M < n then U n j else 0) * (1 / Real.sqrt j)) ≤ A_up * c / Real.sqrt n := by
    intro n hn
    by_cases hMn : M < n
    · simp only [if_pos hMn]; exact hU_row n hn
    · simp only [if_neg hMn, zero_mul, sum_const_zero]
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
      positivity
  have hschur := sum_sq_abs_majorized_kernel_le' (fun n j => if M < n then K_up n j else 0)
    (fun n j => if M < n then U n j else 0) uTop
    (fun j => 1 / Real.sqrt j)
    (fun n => A_up * c / Real.sqrt n)
    (fun _ => 42 * Real.exp (3 / 2) * A_up * c ^ 2 * ((N : ℝ) / M))
    hU_nonneg' hKU'
    (fun j hj => by
      have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Icc.mp hj).1
      positivity)
    hU_row' hU_col
  have hlog2T : 2 * (Real.log (2 * T) + 3) ≤ 16 * (1 + Real.log c) := by
    have he1 : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
    have h2T : 2 * T ≤ 8 * c := by dsimp only [T]; nlinarith only [hc1, he1]
    have hlog8 : Real.log 8 ≤ 5 := by
      have he1' : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      have he5 : (8 : ℝ) ≤ Real.exp 5 := by
        have hp : (2 : ℝ) ^ 5 ≤ (Real.exp 1) ^ 5 := pow_le_pow_left₀ (by norm_num) he1' 5
        rw [← Real.exp_nat_mul] at hp; norm_num at hp; linarith only [hp]
      exact (Real.log_le_log (by norm_num) he5).trans_eq (Real.log_exp 5)
    have hle : Real.log (2 * T) ≤ 5 + Real.log c := by
      calc
        Real.log (2 * T) ≤ Real.log (8 * c) := Real.log_le_log (by positivity) h2T
        _ = Real.log 8 + Real.log c := Real.log_mul (by norm_num) hc0.ne'
        _ ≤ 5 + Real.log c := by linarith only [hlog8]
    have hlc0 := Real.log_nonneg hc1
    linarith only [hle, hlc0]
  have huTop_log :
      Real.log N * (∑ j ∈ Icc 1 N, uTop j ^ 2) ≤ 16 * (1 + Real.log c) * ‖u‖ ^ 2 := by
    have hfilt : (∑ j ∈ Icc 1 N, uTop j ^ 2) =
        ∑ j ∈ (Icc 1 N).filter (fun j : ℕ => (N : ℝ) / j < T), primeHorizonExtension u j ^ 2 := by
      rw [sum_filter]; exact sum_congr rfl fun j _ => by dsimp only [uTop]; split_ifs <;> simp
    rw [hfilt]
    exact (sum_quotient_tail_sq_le_of_mem_conductorSubspace hR hT1 hRNT hlog hu).trans
      (mul_le_mul_of_nonneg_right hlog2T (sq_nonneg _))
  have hlhs : (∑ n ∈ Icc 1 N, if M < n then
        primeHorizonExtension (upwardPrimeVector φ c N u) n ^ 2 else 0) =
      ∑ n ∈ Icc 1 N, (∑ j ∈ Icc 1 N, (if M < n then K_up n j else 0) * uTop j) ^ 2 := by
    refine sum_congr rfl fun n hn => ?_
    by_cases hMn : M < n
    · simp only [if_pos hMn]; rw [hrow_eq n hn]
    · simp only [if_neg hMn, zero_mul, sum_const_zero]; norm_num
  rw [hlhs]
  refine hschur.trans ?_
  rw [← mul_sum]
  have hL0 : 0 < Real.log N := by linarith
  have h1 : (∑ j ∈ Icc 1 N, uTop j ^ 2) ≤ 16 * (1 + Real.log c) / Real.log N * ‖u‖ ^ 2 := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hL0]; linarith
  have hD0 : 0 ≤ 42 * Real.exp (3 / 2) * A_up * c ^ 2 * ((N : ℝ) / M) := by
    have hM0 : (0 : ℝ) < M := by exact_mod_cast hM1
    positivity
  calc _ ≤ 42 * Real.exp (3 / 2) * A_up * c ^ 2 * ((N : ℝ) / M) *
        (16 * (1 + Real.log c) / Real.log N * ‖u‖ ^ 2) := mul_le_mul_of_nonneg_left h1 hD0
    _ = _ := by ring

/-! ### The channel identity of the band–far cross -/

theorem toEuclideanLin_one_apply {N : ℕ} (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    Matrix.toEuclideanLin (1 : Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ) x = x := by
  ext n
  change ((1 : Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ) *ᵥ x) n = x n
  rw [Matrix.one_mulVec]

/-- **Channels of a cross term.** For `⟨x, w⟩ = 0` the complete Weil cross splits into the
prime, center, separated, pole-error, overlap−downward and upward channels. -/
theorem completeWeil_inner_eq_channels {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc0 : 0 < c)
    {N : ℕ} (hN1 : 1 ≤ N) (x w : EuclideanSpace ℝ (PrimeHorizonIndex N)) (hxw : ⟪x, w⟫ = 0) :
    ⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N) x, w⟫ =
      -⟪Matrix.toEuclideanLin (fullPrimeMatrix N) x, w⟫ +
        (⟪Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift φ c) N) x, w⟫ +
          ⟪Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ c N) x, w⟫) -
        ⟪Matrix.toEuclideanLin (separatedCrossErrorMatrix φ c N) x, w⟫ +
        ⟪Matrix.toEuclideanLin (overlapMatrix φ c N) x - downwardPrimeVector φ c N x, w⟫ -
        ⟪upwardPrimeVector φ c N x, w⟫ := by
  rw [completeWeilMatrix_eq_decomposition_at_every_overlap hφ hsupp hM hc0 hN1]
  simp only [map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, toEuclideanLin_one_apply,
    fullWeilNonRatioMatrix_eq_downward_add_upward hφ hsupp hM hc0 hN1 x,
    inner_add_left, inner_sub_left, real_inner_smul_left, hxw, mul_zero]
  ring

/-- **Center plus pole error.** The two pole parts combine into the exact pole coefficient:
`⟨C_α x, w⟩ + ⟨E_pole x, w⟩ = P Σ w_n x_j Π(n, j) − α ⟨Collar x, w⟩`. -/
theorem center_add_poleError_inner_eq (φ : ℝ → ℝ) (c : ℝ) {N : ℕ}
    (x w : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    ⟪Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift φ c) N) x, w⟫ +
        ⟪Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ c N) x, w⟫ =
      exactPoleCoefficient φ c N * (∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N,
          primeHorizonExtension w n * primeHorizonExtension x j * arithmeticPoleKernel n j) -
        completeWeilPoleShift φ c *
          ⟪Matrix.toEuclideanLin (horizonKernelMatrix (collarKernel N) N) x, w⟫ := by
  have h1 : fullWeilCenterMatrix (completeWeilPoleShift φ c) N = horizonKernelMatrix
      (fun n j => (completeWeilPoleShift φ c / N) *
        (arithmeticPoleKernel n j - archimedeanCenterKernel n j)) N := rfl
  have h2 : fullWeilPoleErrorMatrix φ c N = horizonKernelMatrix
      (fun n j => atomPoleErrorCoefficient φ c N * arithmeticPoleKernel n j) N := rfl
  rw [h1, h2, horizonKernelMatrix_bilinear, horizonKernelMatrix_bilinear,
    horizonKernelMatrix_bilinear, exactPoleCoefficient_eq, mul_sum, mul_sum, ← sum_add_distrib,
    ← sum_sub_distrib]
  refine sum_congr rfl fun n _ => ?_
  rw [mul_sum, mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
  refine sum_congr rfl fun j _ => ?_
  unfold collarKernel
  ring

/-- The pole-free part of a band: `u = a₁ v₁ + ũ`. -/
theorem band_eq_pole_add_reduced {R N : ℕ} (hR : 1 ≤ R) (a : ℕ → ℝ) :
    (∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N) =
      a 1 • normalizedRamanujanHorizonVector 1 N +
        ∑ m ∈ Icc 1 R, (if m = 1 then 0 else a m) • normalizedRamanujanHorizonVector m N := by
  have h1 : (1 : ℕ) ∈ Icc 1 R := mem_Icc.mpr ⟨le_rfl, hR⟩
  rw [← add_sum_erase _ _ h1, ← add_sum_erase _ _ h1, if_pos rfl, zero_smul, zero_add]
  congr 1
  exact sum_congr rfl fun m hm => by rw [if_neg (ne_of_mem_erase hm)]

theorem divisorJetCoeff_one_reduced (R : ℕ) (a : ℕ → ℝ) :
    divisorJetCoeff R (fun m => if m = 1 then 0 else a m) 1 = divisorJetCoeff R a 1 := by
  rw [divisorJetCoeff_one_eq, divisorJetCoeff_one_eq]
  refine sum_congr rfl fun m _ => ?_
  by_cases h : m = 1
  · subst h; simp
  · simp only [if_neg h]

/-! ### Payment arithmetic -/

/-- `Z² ≤ F W²` pays `2|Z| ≤ F/γ + γW²`. -/
theorem two_abs_le_of_sq_le {Z F W γ : ℝ} (hF : 0 ≤ F) (hγ : 0 < γ) (h : Z ^ 2 ≤ F * W ^ 2) :
    2 * |Z| ≤ F / γ + γ * W ^ 2 := by
  have hA : 0 ≤ F / γ + γ * W ^ 2 := by positivity
  have hsq : (2 * |Z|) ^ 2 ≤ (F / γ + γ * W ^ 2) ^ 2 := by
    have e : (F / γ + γ * W ^ 2) ^ 2 = (F / γ - γ * W ^ 2) ^ 2 + 4 * F * W ^ 2 := by
      field_simp; ring
    rw [e, mul_pow, sq_abs]
    nlinarith [sq_nonneg (F / γ - γ * W ^ 2)]
  have h2 : 0 ≤ 2 * |Z| := by positivity
  exact pow_le_pow_iff_left₀ h2 hA two_ne_zero |>.mp hsq

/-- Cauchy–Schwarz payment on a row block: `2|Σ_S f w| ≤ (Σ_S f²)/s + s Σ_S w²`. -/
theorem two_abs_sum_mul_le (T : Finset ℕ) (f g : ℕ → ℝ) {s : ℝ} (hs : 0 < s) :
    2 * |∑ n ∈ T, f n * g n| ≤ (∑ n ∈ T, f n ^ 2) / s + s * ∑ n ∈ T, g n ^ 2 := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq T f g
  have hF : 0 ≤ ∑ n ∈ T, f n ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  have hG : 0 ≤ ∑ n ∈ T, g n ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  have := two_abs_le_of_sq_le (Z := ∑ n ∈ T, f n * g n) (W := Real.sqrt (∑ n ∈ T, g n ^ 2))
    hF hs (by rw [Real.sq_sqrt hG]; exact hcs)
  rwa [Real.sq_sqrt hG] at this

theorem six_sq_le (x₁ x₂ x₃ x₄ x₅ x₆ : ℝ) :
    (x₁ + x₂ - x₃ - x₄ + x₅ + x₆) ^ 2 ≤
      6 * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2 + x₄ ^ 2 + x₅ ^ 2 + x₆ ^ 2) := by
  nlinarith [sq_nonneg (x₁ - x₂), sq_nonneg (x₁ + x₃), sq_nonneg (x₁ + x₄), sq_nonneg (x₁ - x₅),
    sq_nonneg (x₁ - x₆), sq_nonneg (x₂ + x₃), sq_nonneg (x₂ + x₄), sq_nonneg (x₂ - x₅),
    sq_nonneg (x₂ - x₆), sq_nonneg (x₃ - x₄), sq_nonneg (x₃ + x₅), sq_nonneg (x₃ + x₆),
    sq_nonneg (x₄ + x₅), sq_nonneg (x₄ + x₆), sq_nonneg (x₅ - x₆)]

/-- **The cross arithmetic.** Six channels paid by `γW²`, the prime channel by its own bound,
and the two upward blocks by the prefix and top masses. -/
theorem band_far_cross_arith {X Pr z₁ z₂ z₃ z₄ z₅ z₆ UP US BP F₁ F₂ F₃ F₄ F₅ F₆ FP FS P S W γ s t : ℝ}
    (hX : X = -Pr + (z₁ + z₂ - z₃ - z₄ + z₅ + z₆) - UP - US)
    (hPr : 2 * |Pr| ≤ BP)
    (h₁ : z₁ ^ 2 ≤ F₁ * W ^ 2) (h₂ : z₂ ^ 2 ≤ F₂ * W ^ 2) (h₃ : z₃ ^ 2 ≤ F₃ * W ^ 2)
    (h₄ : z₄ ^ 2 ≤ F₄ * W ^ 2) (h₅ : z₅ ^ 2 ≤ F₅ * W ^ 2) (h₆ : z₆ ^ 2 ≤ F₆ * W ^ 2)
    (hF₁ : 0 ≤ F₁) (hF₂ : 0 ≤ F₂) (hF₃ : 0 ≤ F₃) (hF₄ : 0 ≤ F₄) (hF₅ : 0 ≤ F₅) (hF₆ : 0 ≤ F₆)
    (hUP : 2 * |UP| ≤ FP / s + s * P) (hUS : 2 * |US| ≤ FS / t + t * S) (hγ : 0 < γ) :
    2 * |X| ≤ BP + 6 * (F₁ + F₂ + F₃ + F₄ + F₅ + F₆) / γ + γ * W ^ 2 +
      (FP / s + s * P) + (FS / t + t * S) := by
  have hZ := six_sq_le z₁ z₂ z₃ z₄ z₅ z₆
  have hW := sq_nonneg W
  have hZ' : (z₁ + z₂ - z₃ - z₄ + z₅ + z₆) ^ 2 ≤ 6 * (F₁ + F₂ + F₃ + F₄ + F₅ + F₆) * W ^ 2 := by
    nlinarith
  have hpay := two_abs_le_of_sq_le (by positivity) hγ hZ'
  rw [hX]
  have := abs_sub (-Pr + (z₁ + z₂ - z₃ - z₄ + z₅ + z₆) - UP) US
  have := abs_sub (-Pr + (z₁ + z₂ - z₃ - z₄ + z₅ + z₆)) UP
  have := abs_add_le (-Pr) (z₁ + z₂ - z₃ - z₄ + z₅ + z₆)
  rw [abs_neg] at this
  linarith

theorem inner_eq_sum_primeHorizonExtension {N : ℕ} (x y : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    ⟪x, y⟫ = ∑ n ∈ Icc 1 N, primeHorizonExtension x n * primeHorizonExtension y n := by
  have h : ⟪x, y⟫ = ∑ i : PrimeHorizonIndex N, x i * y i := by
    simp [PiLp.inner_apply, mul_comm]
  rw [h, ← sum_coe_sort (Icc 1 N)]
  exact sum_congr rfl fun i _ => by rw [primeHorizonExtension_coe, primeHorizonExtension_coe]

theorem inner_eq_sum_Icc_add_Ioc {N M : ℕ} (hM1 : 1 ≤ M) (hMN : M ≤ N)
    (x y : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    ⟪x, y⟫ = (∑ n ∈ Icc 1 M, primeHorizonExtension x n * primeHorizonExtension y n) +
      ∑ n ∈ Ioc M N, primeHorizonExtension x n * primeHorizonExtension y n := by
  have hu : Icc 1 N = Icc 1 M ∪ Ioc M N := by
    ext n; simp only [mem_union, mem_Icc, mem_Ioc]; omega
  rw [inner_eq_sum_primeHorizonExtension, hu, sum_union]
  rw [Finset.disjoint_left]
  intro n h1 h2
  have := (mem_Icc.mp h1).2
  have := (mem_Ioc.mp h2).1
  omega

/-! ### The band–far cross channel by channel -/

/-- The band without its pole conductor. -/
def poleFreeBand (R N : ℕ) (a : ℕ → ℝ) : EuclideanSpace ℝ (PrimeHorizonIndex N) :=
  ∑ m ∈ Icc 1 R, (if m = 1 then 0 else a m) • normalizedRamanujanHorizonVector m N

/-- The residual `W v₁ − E₁ v₁` of the pole mode. -/
def poleModeResidual (c : ℝ) (N : ℕ) : EuclideanSpace ℝ (PrimeHorizonIndex N) :=
  Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
      (normalizedRamanujanHorizonVector 1 N) -
    completedConductorEnergy tiltedUnitSpline c 1 • normalizedRamanujanHorizonVector 1 N

/-- The coherent pole pair `P⟨Πũ, w⟩ + J₁⟨K₂ᵦ v₁, w⟩`. -/
def coherentPolePair (c : ℝ) (R N : ℕ) (a : ℕ → ℝ) (w : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    ℝ :=
  exactPoleCoefficient tiltedUnitSpline c N *
      (∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N, primeHorizonExtension w n *
        primeHorizonExtension (poleFreeBand R N a) j * arithmeticPoleKernel n j) +
    divisorJetCoeff R a 1 * ⟪Matrix.toEuclideanLin (nearDivisorJetKernelMatrix tiltedUnitSpline c N)
      (normalizedRamanujanHorizonVector 1 N), w⟫

/-- `(Overlap − Down)ũ − K₂ᵦ v_jet(ũ)`. -/
def nearRemainder (c : ℝ) (R N : ℕ) (a : ℕ → ℝ) : EuclideanSpace ℝ (PrimeHorizonIndex N) :=
  Matrix.toEuclideanLin (overlapMatrix tiltedUnitSpline c N) (poleFreeBand R N a) -
    downwardPrimeVector tiltedUnitSpline c N (poleFreeBand R N a) -
    Matrix.toEuclideanLin (nearDivisorJetKernelMatrix tiltedUnitSpline c N)
      (divisorJetHorizonVector R N (fun m => if m = 1 then 0 else a m))

/-- **The channel identity of the band–far cross.** -/
theorem band_far_cross_eq {R M N : ℕ} {c : ℝ} (hR : 1 ≤ R) (hM1 : 1 ≤ M) (hMN : M ≤ N)
    (hc0 : 0 < c) (hN1 : 1 ≤ N) (a : ℕ → ℝ) {w : EuclideanSpace ℝ (PrimeHorizonIndex N)}
    (hw : w ∈ (conductorSubspace R N)ᗮ) :
    ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
        (∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N), w⟫ =
      -⟪Matrix.toEuclideanLin (fullPrimeMatrix N) (poleFreeBand R N a), w⟫ +
        (a 1 * ⟪poleModeResidual c N, w⟫ + coherentPolePair c R N a w -
          completeWeilPoleShift tiltedUnitSpline c *
            ⟪Matrix.toEuclideanLin (horizonKernelMatrix (collarKernel N) N) (poleFreeBand R N a), w⟫ -
          ⟪Matrix.toEuclideanLin (separatedCrossErrorMatrix tiltedUnitSpline c N)
            (poleFreeBand R N a), w⟫ +
          ⟪nearRemainder c R N a, w⟫ +
          ⟪Matrix.toEuclideanLin (nearDivisorJetKernelMatrix tiltedUnitSpline c N)
            (reducedDivisorJet R N (fun m => if m = 1 then 0 else a m)), w⟫) -
        (∑ n ∈ Icc 1 M, primeHorizonExtension
          (upwardPrimeVector tiltedUnitSpline c N (poleFreeBand R N a)) n * primeHorizonExtension w n) -
        (∑ n ∈ Ioc M N, primeHorizonExtension
          (upwardPrimeVector tiltedUnitSpline c N (poleFreeBand R N a)) n * primeHorizonExtension w n) := by
  have hmem : poleFreeBand R N a ∈ conductorSubspace R N :=
    sum_normalizedRamanujanHorizonVector_mem_conductorSubspace R N _
  have huTw : ⟪poleFreeBand R N a, w⟫ = 0 := Submodule.inner_right_of_mem_orthogonal hmem hw
  have hv1w : ⟪normalizedRamanujanHorizonVector 1 N, w⟫ = 0 := Submodule.inner_right_of_mem_orthogonal
    (mem_conductorSubspace_normalizedRamanujanHorizonVector (mem_Icc.mpr ⟨le_rfl, hR⟩)) hw
  have hsplit : (∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N) =
      a 1 • normalizedRamanujanHorizonVector 1 N + poleFreeBand R N a :=
    band_eq_pole_add_reduced hR a
  have hWv1 : ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
      (normalizedRamanujanHorizonVector 1 N), w⟫ = ⟪poleModeResidual c N, w⟫ := by
    rw [poleModeResidual, inner_sub_left, real_inner_smul_left, hv1w, mul_zero, sub_zero]
  have hch := completeWeil_inner_eq_channels contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero
    integral_tiltedUnitSpline_sq_pos hc0 hN1 (poleFreeBand R N a) w huTw
  have hcp := center_add_poleError_inner_eq tiltedUnitSpline c (poleFreeBand R N a) w
  have hjetv := divisorJetHorizonVector_eq_reduced_add hR N (fun m => if m = 1 then 0 else a m)
  have hOD : ⟪Matrix.toEuclideanLin (overlapMatrix tiltedUnitSpline c N) (poleFreeBand R N a) -
      downwardPrimeVector tiltedUnitSpline c N (poleFreeBand R N a), w⟫ =
      ⟪nearRemainder c R N a, w⟫ +
        ⟪Matrix.toEuclideanLin (nearDivisorJetKernelMatrix tiltedUnitSpline c N)
          (reducedDivisorJet R N (fun m => if m = 1 then 0 else a m)), w⟫ +
        divisorJetCoeff R a 1 * ⟪Matrix.toEuclideanLin (nearDivisorJetKernelMatrix tiltedUnitSpline c N)
          (normalizedRamanujanHorizonVector 1 N), w⟫ := by
    have e : Matrix.toEuclideanLin (overlapMatrix tiltedUnitSpline c N) (poleFreeBand R N a) -
        downwardPrimeVector tiltedUnitSpline c N (poleFreeBand R N a) =
        nearRemainder c R N a + Matrix.toEuclideanLin (nearDivisorJetKernelMatrix tiltedUnitSpline c N)
          (divisorJetHorizonVector R N (fun m => if m = 1 then 0 else a m)) := by
      rw [nearRemainder]; abel
    rw [e, inner_add_left, hjetv, map_add, map_smul, inner_add_left, real_inner_smul_left,
      divisorJetCoeff_one_reduced]
    ring
  have hUp := inner_eq_sum_Icc_add_Ioc hM1 hMN
    (upwardPrimeVector tiltedUnitSpline c N (poleFreeBand R N a)) w
  rw [hsplit, map_add, map_smul, inner_add_left, real_inner_smul_left, hWv1, hch, hcp, hOD, hUp]
  unfold coherentPolePair
  ring

theorem inner_sq_le_norm_sq_mul {N : ℕ} (x w : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    ⟪x, w⟫ ^ 2 ≤ ‖x‖ ^ 2 * ‖w‖ ^ 2 := by
  have h := pow_le_pow_left₀ (abs_nonneg _) (abs_real_inner_le_norm x w) 2
  rwa [sq_abs, mul_pow] at h

/-- The pole-free band has at most three times the band mass. -/
theorem norm_poleFreeBand_sq_le {R N : ℕ} (hR : 2 ≤ R) (hRR : R * R ≤ N)
    (hlog : 18 * (1 + Real.log R) ≤ Real.log N) (a : ℕ → ℝ) :
    ‖poleFreeBand R N a‖ ^ 2 ≤ 3 * ‖∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 := by
  have h1 := (half_and_three_halves_riesz_of_log_le hR hRR hlog a).1
  have h2 := (half_and_three_halves_riesz_of_log_le hR hRR hlog
    (fun m => if m = 1 then 0 else a m)).2
  have hle : (∑ m ∈ Icc 1 R, (if m = 1 then 0 else a m) ^ 2) ≤ ∑ m ∈ Icc 1 R, a m ^ 2 :=
    sum_le_sum fun m _ => by split_ifs <;> simp [sq_nonneg]
  unfold poleFreeBand
  linarith

/-- **Pole-mode channel.** `(a₁⟨r₁, w⟩)² ≤ 1296 ((1 + log R)/log N)² ρ ‖u‖² ‖w‖²`. -/
theorem poleMode_channel_sq_le {R N : ℕ} {c ρ : ℝ} (hR : 2 ≤ R) (hRR : R * R ≤ N)
    (hlog : 18 * (1 + Real.log R) ≤ Real.log N) (hρ : ‖poleModeResidual c N‖ ^ 2 ≤ ρ)
    (a : ℕ → ℝ)
    (hu1 : (∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N) ∈ (conductorSubspace 1 N)ᗮ)
    (w : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    (a 1 * ⟪poleModeResidual c N, w⟫) ^ 2 ≤
      (1296 * ((1 + Real.log R) / Real.log N) ^ 2 * ρ *
        ‖∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N‖ ^ 2) * ‖w‖ ^ 2 := by
  have h := (low_band_norm_le_of_mem_orthogonal (by omega : 1 ≤ 1) (by omega : 1 ≤ R)
    hR hRR hlog hu1).1
  rw [Icc_self, sum_singleton, Real.sqrt_sq_eq_abs] at h
  have ha1 := pow_le_pow_left₀ (abs_nonneg _) h 2
  rw [sq_abs, mul_pow] at ha1
  have hr := (inner_sq_le_norm_sq_mul (poleModeResidual c N) w).trans
    (mul_le_mul_of_nonneg_right hρ (sq_nonneg _))
  rw [mul_pow]
  calc a 1 ^ 2 * ⟪poleModeResidual c N, w⟫ ^ 2 ≤
      ((36 * (1 + Real.log R) / Real.log N) ^ 2 *
        ‖∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N‖ ^ 2) * (ρ * ‖w‖ ^ 2) :=
        mul_le_mul ha1 hr (sq_nonneg _) (by positivity)
    _ = _ := by ring

/-- **Collar channel.** `(α⟨C ũ, w⟩)² ≤ c²(24 + 780 Sg₁ + 72R^{15}/N)/log N · ‖u‖² ‖w‖²`. -/
theorem collar_channel_sq_le {R N : ℕ} {c Sg₁ : ℝ} (hR : 2 ≤ R) (hR6 : R ^ 6 ≤ N)
    (hlog : 18 * (1 + Real.log R) ≤ Real.log N) (hc0 : 0 < c) (hSg0 : 0 ≤ Sg₁)
    (hSg : ∀ m ∈ Icc 2 R, (m : ℝ) / m.totient ≤ Sg₁) (a : ℕ → ℝ)
    (w : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    (completeWeilPoleShift tiltedUnitSpline c *
        ⟪Matrix.toEuclideanLin (horizonKernelMatrix (collarKernel N) N) (poleFreeBand R N a), w⟫) ^ 2 ≤
      (c ^ 2 * (24 + 780 * Sg₁ + 72 * (R : ℝ) ^ 15 / N) / Real.log N *
        ‖∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N‖ ^ 2) * ‖w‖ ^ 2 := by
  have hα0 : 0 ≤ completeWeilPoleShift tiltedUnitSpline c :=
    completeWeilPoleShift_nonneg tiltedUnitSpline hc0.le
  have hαc : completeWeilPoleShift tiltedUnitSpline c ≤ c :=
    completeWeilPoleShift_le contDiff_tiltedUnitSpline.continuous
      tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos hc0.le
  have hcol := collar_reducedBand_sq_le hR hR6 hlog a hSg0 hSg
  have hb := (inner_sq_le_norm_sq_mul _ w).trans (mul_le_mul_of_nonneg_right hcol (sq_nonneg _))
  rw [mul_pow]
  have hα2 := pow_le_pow_left₀ hα0 hαc 2
  calc _ ≤ c ^ 2 * ((24 + 780 * Sg₁ + 72 * (R : ℝ) ^ 15 / N) / Real.log N *
        ‖∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 * ‖w‖ ^ 2) :=
        mul_le_mul hα2 hb (sq_nonneg _) (sq_nonneg _)
    _ = _ := by ring

/-- **Separated channel.** -/
theorem sep_channel_sq_le {R N : ℕ} {c : ℝ} (hR : 2 ≤ R) (hR6 : R ^ 6 ≤ N)
    (hlog : 18 * (1 + Real.log R) ≤ Real.log N) (hc0 : 0 < c) (a : ℕ → ℝ)
    (w : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    ⟪Matrix.toEuclideanLin (separatedCrossErrorMatrix tiltedUnitSpline c N)
        (poleFreeBand R N a), w⟫ ^ 2 ≤
      (3 * (520 * (152 * (∫ t, |tiltedUnitSpline t|) ^ 2 / (∫ t, tiltedUnitSpline t ^ 2)) ^ 2) *
        (c ^ 4 / Real.log N) * ‖∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N‖ ^ 2) *
        ‖w‖ ^ 2 := by
  have hR4 : R ^ 4 ≤ N := (Nat.pow_le_pow_right (by omega : 0 < R) (by norm_num : 4 ≤ 6)).trans hR6
  have hRR : R * R ≤ N := by
    have hh := (Nat.pow_le_pow_right (by omega : 0 < R) (by norm_num : 2 ≤ 6)).trans hR6
    simpa only [sq] using hh
  have hmem : poleFreeBand R N a ∈ conductorSubspace R N :=
    sum_normalizedRamanujanHorizonVector_mem_conductorSubspace R N _
  have hsep := norm_separatedCrossErrorMatrix_sq_le_of_mem_conductorSubspace
    contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos
    hc0 hR hR4 hlog hmem
  have hT := norm_poleFreeBand_sq_le hR hRR hlog a
  have hL : 0 < Real.log N := by linarith [Real.log_natCast_nonneg R]
  refine (inner_sq_le_norm_sq_mul _ w).trans (mul_le_mul_of_nonneg_right (hsep.trans ?_) (sq_nonneg _))
  have h0 : 0 ≤ 520 * (152 * (∫ t, |tiltedUnitSpline t|) ^ 2 / (∫ t, tiltedUnitSpline t ^ 2)) ^ 2 *
      (c ^ 4 / Real.log N) := by positivity
  calc _ ≤ 520 * (152 * (∫ t, |tiltedUnitSpline t|) ^ 2 / (∫ t, tiltedUnitSpline t ^ 2)) ^ 2 *
        (c ^ 4 / Real.log N) * (3 * ‖∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hT h0
    _ = _ := by ring

theorem exists_sep_channel_sq_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {R N : ℕ} {c : ℝ}, 2 ≤ R → R ^ 6 ≤ N →
      18 * (1 + Real.log R) ≤ Real.log N → 0 < c → ∀ (a : ℕ → ℝ)
      (w : EuclideanSpace ℝ (PrimeHorizonIndex N)),
      ⟪Matrix.toEuclideanLin (separatedCrossErrorMatrix tiltedUnitSpline c N)
          (poleFreeBand R N a), w⟫ ^ 2 ≤
        (C * (c ^ 4 / Real.log N) *
          ‖∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N‖ ^ 2) * ‖w‖ ^ 2 :=
  ⟨_, by positivity, fun hR hR6 hlog hc0 a w => sep_channel_sq_le hR hR6 hlog hc0 a w⟩

/-- **Near remainder channel.** -/
theorem exists_nearRemainder_channel_sq_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {R N : ℕ} {c : ℝ}, 2 ≤ R → R * R ≤ N →
      18 * (1 + Real.log R) ≤ Real.log N → 1 ≤ c → c / N ≤ 1 / 3 →
      ((R * R : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ N → ∀ (a : ℕ → ℝ)
      (w : EuclideanSpace ℝ (PrimeHorizonIndex N)),
      ⟪nearRemainder c R N a, w⟫ ^ 2 ≤
        (C * ((c ^ 4 * (1 + Real.log c) / Real.log N + c ^ 3 * (R : ℝ) ^ 2 * (Real.log N / N)) *
          ‖∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N‖ ^ 2)) * ‖w‖ ^ 2 := by
  obtain ⟨C_near, hC_near, hnear⟩ := exists_overlap_sub_downward_sub_jet_sq_le
    contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos
  refine ⟨3 * C_near, by positivity, ?_⟩
  intro R N c hR hRR hlog hc1 hw3 hsize a w
  have hn := hnear hR hRR hlog hc1 hw3 hsize (fun m => if m = 1 then 0 else a m)
  have hT := norm_poleFreeBand_sq_le hR hRR hlog a
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hL : 0 < Real.log N := by linarith [Real.log_natCast_nonneg R]
  have hN0 : (0 : ℝ) < N := by
    have : 0 < N := by
      rcases Nat.eq_zero_or_pos N with h | h
      · rw [h, Nat.cast_zero, Real.log_zero] at hL; exact absurd hL (lt_irrefl 0)
      · exact h
    exact_mod_cast this
  refine (inner_sq_le_norm_sq_mul _ w).trans (mul_le_mul_of_nonneg_right ?_ (sq_nonneg _))
  have hlc := Real.log_nonneg hc1
  have h0 : 0 ≤ C_near * (c ^ 4 * (1 + Real.log c) / Real.log N +
      c ^ 3 * (R : ℝ) ^ 2 * (Real.log N / N)) := by positivity
  calc ‖nearRemainder c R N a‖ ^ 2 ≤ C_near * ((c ^ 4 * (1 + Real.log c) / Real.log N +
        c ^ 3 * (R : ℝ) ^ 2 * (Real.log N / N)) * ‖poleFreeBand R N a‖ ^ 2) := hn
    _ = C_near * (c ^ 4 * (1 + Real.log c) / Real.log N +
        c ^ 3 * (R : ℝ) ^ 2 * (Real.log N / N)) * ‖poleFreeBand R N a‖ ^ 2 := by ring
    _ ≤ C_near * (c ^ 4 * (1 + Real.log c) / Real.log N +
        c ^ 3 * (R : ℝ) ^ 2 * (Real.log N / N)) *
        (3 * ‖∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hT h0
    _ = _ := by ring

/-- **Reduced jet channel.** -/
theorem exists_reducedJet_channel_sq_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {R N : ℕ} {c Sg₁ : ℝ}, 2 ≤ R →
      18 * (1 + Real.log R) ≤ Real.log N → 1 ≤ c → c / N ≤ 1 →
      4 * (linearNearRowRadius c + 1) ^ 2 ≤ N →
      ⌈linearNearRowRadius c⌉₊ + 1 ≤ N → R * R ≤ N / (⌈linearNearRowRadius c⌉₊ + 1) →
      1 ≤ Sg₁ → (∀ m ∈ Icc 2 R, (m : ℝ) / m.totient ≤ Sg₁) → ∀ (a : ℕ → ℝ)
      (w : EuclideanSpace ℝ (PrimeHorizonIndex N)),
      ⟪Matrix.toEuclideanLin (nearDivisorJetKernelMatrix tiltedUnitSpline c N)
          (reducedDivisorJet R N (fun m => if m = 1 then 0 else a m)), w⟫ ^ 2 ≤
        (C * c * (Sg₁ ^ 2 * (1 + Real.log c) / Real.log N + c ^ 5 / N +
          c ^ 3 * (R : ℝ) ^ 4 / (N * Real.log N)) * (1 + Real.log R) *
          ∑ m ∈ Icc 1 R, (1 + Real.log m) * a m ^ 2) * ‖w‖ ^ 2 := by
  obtain ⟨C_jet, hC_jet, hjet⟩ := exists_nearGram_reducedDivisorJet_sq_le_weighted
    contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos
  refine ⟨C_jet, hC_jet, ?_⟩
  intro R N c Sg₁ hR hlog hc1 hw1 hrad hceil hRK hSg1 hSg a w
  have hSgσ : ∀ m ∈ Icc 2 R, (ArithmeticFunction.sigma 1 m : ℝ) / m.totient ≤ Sg₁ ^ 2 := by
    intro m hm
    have hm1 : 1 ≤ m := by have := (mem_Icc.mp hm).1; omega
    have hq0 : 0 ≤ (m : ℝ) / m.totient := by positivity
    exact (sigma_div_totient_le_sq hm1).trans (pow_le_pow_left₀ hq0 (hSg m hm) 2)
  have hjt := hjet hR hlog hc1 hw1 hrad hceil hRK (Sg := Sg₁ ^ 2) (by nlinarith) hSgσ
    (fun m => if m = 1 then 0 else a m)
  have hGT : (∑ m ∈ Icc 1 R, (1 + Real.log m) * (if m = 1 then 0 else a m) ^ 2) ≤
      ∑ m ∈ Icc 1 R, (1 + Real.log m) * a m ^ 2 :=
    sum_le_sum fun m _ => by
      split_ifs
      · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero]
        exact mul_nonneg (by linarith [Real.log_natCast_nonneg m]) (sq_nonneg _)
      · exact le_rfl
  refine (inner_sq_le_norm_sq_mul _ w).trans (mul_le_mul_of_nonneg_right (hjt.trans ?_) (sq_nonneg _))
  have e : (1 + Real.log c) * Sg₁ ^ 2 / Real.log N = Sg₁ ^ 2 * (1 + Real.log c) / Real.log N := by
    ring
  rw [e]
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hL : 0 < Real.log N := by linarith [Real.log_natCast_nonneg R]
  have hlc := Real.log_nonneg hc1
  have hlR := Real.log_natCast_nonneg R
  have : 0 ≤ C_jet * c * (Sg₁ ^ 2 * (1 + Real.log c) / Real.log N + c ^ 5 / N +
      c ^ 3 * (R : ℝ) ^ 4 / (N * Real.log N)) * (1 + Real.log R) := by positivity
  exact mul_le_mul_of_nonneg_left hGT this

/-- **Upward prefix channel.** -/
theorem exists_upward_prefix_channel_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {R M N : ℕ} {c : ℝ}, 2 ≤ R → R * R ≤ N →
      18 * (1 + Real.log R) ≤ Real.log N → 1 ≤ c → c / N ≤ 1 / 3 →
      ((R * R : ℕ) + 1 : ℝ) * (c * Real.exp 1 + 1) ≤ N → M ≤ N → ∀ (a : ℕ → ℝ)
      (w : EuclideanSpace ℝ (PrimeHorizonIndex N)) {s : ℝ}, 0 < s →
      2 * |∑ n ∈ Icc 1 M, primeHorizonExtension
          (upwardPrimeVector tiltedUnitSpline c N (poleFreeBand R N a)) n *
            primeHorizonExtension w n| ≤
        C * c ^ 2 * (1 + Real.log c) *
            ‖∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 / s +
          s * ∑ n ∈ Icc 1 M, primeHorizonExtension w n ^ 2 := by
  obtain ⟨C_up0, hC_up0, hup⟩ := exists_upwardPrimeVector_norm_le_of_mem_conductorSubspace
    contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos
  refine ⟨3 * C_up0 ^ 2, by positivity, ?_⟩
  intro R M N c hR hRR hlog hc1 hw3 hsize hMN a w s hs
  have hmem : poleFreeBand R N a ∈ conductorSubspace R N :=
    sum_normalizedRamanujanHorizonVector_mem_conductorSubspace R N _
  have hn := hup hR hlog hc1 hw3 hsize hmem
  have hT := norm_poleFreeBand_sq_le hR hRR hlog a
  have hpay := two_abs_sum_mul_le (Icc 1 M)
    (primeHorizonExtension (upwardPrimeVector tiltedUnitSpline c N (poleFreeBand R N a)))
    (primeHorizonExtension w) hs
  suffices hX : (∑ n ∈ Icc 1 M, primeHorizonExtension
      (upwardPrimeVector tiltedUnitSpline c N (poleFreeBand R N a)) n ^ 2) ≤
      3 * C_up0 ^ 2 * c ^ 2 * (1 + Real.log c) *
        ‖∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 by
    have := div_le_div_of_nonneg_right hX hs.le
    linarith
  have hsub : (∑ n ∈ Icc 1 M, primeHorizonExtension
      (upwardPrimeVector tiltedUnitSpline c N (poleFreeBand R N a)) n ^ 2) ≤
      ‖upwardPrimeVector tiltedUnitSpline c N (poleFreeBand R N a)‖ ^ 2 := by
    rw [← sum_primeHorizonExtension_sq]
    exact sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc le_rfl hMN) fun _ _ _ => sq_nonneg _
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hlc := Real.log_nonneg hc1
  have hn2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
  rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by linarith)] at hn2
  refine hsub.trans (hn2.trans ?_)
  have h0 : 0 ≤ C_up0 ^ 2 * c ^ 2 * (1 + Real.log c) := by positivity
  calc C_up0 ^ 2 * c ^ 2 * (1 + Real.log c) * ‖poleFreeBand R N a‖ ^ 2 ≤
      C_up0 ^ 2 * c ^ 2 * (1 + Real.log c) *
        (3 * ‖∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hT h0
    _ = _ := by ring

/-- **Upward top channel.** -/
theorem exists_upward_top_channel_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {R M N : ℕ} {c : ℝ}, 2 ≤ R → R * R ≤ N →
      18 * (1 + Real.log R) ≤ Real.log N → 1 ≤ c → c / N ≤ 1 / 3 →
      ((R * R : ℕ) + 1 : ℝ) * (c * Real.exp 1 + 1) ≤ N → 1 ≤ M → ∀ (a : ℕ → ℝ)
      (w : EuclideanSpace ℝ (PrimeHorizonIndex N)) {t : ℝ}, 0 < t →
      2 * |∑ n ∈ Ioc M N, primeHorizonExtension
          (upwardPrimeVector tiltedUnitSpline c N (poleFreeBand R N a)) n *
            primeHorizonExtension w n| ≤
        C * c ^ 2 * ((N : ℝ) / M) * (1 + Real.log c) / Real.log N *
            ‖∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 / t +
          t * ∑ n ∈ Ioc M N, primeHorizonExtension w n ^ 2 := by
  obtain ⟨C_upT0, hC_upT0, hupT⟩ := exists_upwardPrimeVector_top_sq_le
    contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos
  refine ⟨3 * C_upT0, by positivity, ?_⟩
  intro R M N c hR hRR hlog hc1 hw3 hsize hM1 a w t ht
  have hmem : poleFreeBand R N a ∈ conductorSubspace R N :=
    sum_normalizedRamanujanHorizonVector_mem_conductorSubspace R N _
  have hn := hupT hR hlog hc1 hw3 hsize hM1 hmem
  have hT := norm_poleFreeBand_sq_le hR hRR hlog a
  have hpay := two_abs_sum_mul_le (Ioc M N)
    (primeHorizonExtension (upwardPrimeVector tiltedUnitSpline c N (poleFreeBand R N a)))
    (primeHorizonExtension w) ht
  suffices hX : (∑ n ∈ Ioc M N, primeHorizonExtension
      (upwardPrimeVector tiltedUnitSpline c N (poleFreeBand R N a)) n ^ 2) ≤
      3 * C_upT0 * c ^ 2 * ((N : ℝ) / M) * (1 + Real.log c) / Real.log N *
        ‖∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 by
    have := div_le_div_of_nonneg_right hX ht.le
    linarith
  have hIoc : (∑ n ∈ Ioc M N, primeHorizonExtension
      (upwardPrimeVector tiltedUnitSpline c N (poleFreeBand R N a)) n ^ 2) =
      ∑ n ∈ Icc 1 N, if M < n then primeHorizonExtension
        (upwardPrimeVector tiltedUnitSpline c N (poleFreeBand R N a)) n ^ 2 else 0 := by
    rw [← sum_filter]
    congr 1
    ext n; simp only [mem_Ioc, mem_filter, mem_Icc]; omega
  rw [hIoc]
  refine hn.trans ?_
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hlc := Real.log_nonneg hc1
  have hL : 0 < Real.log N := by linarith [Real.log_natCast_nonneg R]
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM1
  have h0 : 0 ≤ C_upT0 * c ^ 2 * ((N : ℝ) / M) * (1 + Real.log c) / Real.log N := by positivity
  calc C_upT0 * c ^ 2 * ((N : ℝ) / M) * (1 + Real.log c) / Real.log N * ‖poleFreeBand R N a‖ ^ 2
      ≤ C_upT0 * c ^ 2 * ((N : ℝ) / M) * (1 + Real.log c) / Real.log N *
        (3 * ‖∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hT h0
    _ = _ := by ring

/-- **Prime channel on the pole-free band.** -/
theorem exists_prime_channel_le :
    ∃ C : ℝ, 0 < C ∧ ∀ {R M N : ℕ}, 2 ≤ R → 2 ≤ N → M ≤ N → ∀ (a : ℕ → ℝ)
      {w : EuclideanSpace ℝ (PrimeHorizonIndex N)}, w ∈ (conductorSubspace R N)ᗮ →
      ∀ {s t : ℝ}, 0 < s → 0 < t →
      2 * |⟪Matrix.toEuclideanLin (fullPrimeMatrix N) (poleFreeBand R N a), w⟫| ≤
        C * ((1 + Real.log R) * (∑ m ∈ Icc 1 R, a m ^ 2) +
            (1 + Real.log R) ^ 2 * primeAdjunctionMass R a) / (Real.log N * s) +
          C * ((1 + Real.log R) * (∑ m ∈ Icc 1 R, a m ^ 2) +
            (1 + Real.log R) * terminalPacketCost R M N * primeAdjunctionMass R a) /
              (Real.log N * t) +
          s * (∑ n ∈ Icc 1 M, primeHorizonExtension w n ^ 2) +
          t * (∑ n ∈ Ioc M N, primeHorizonExtension w n ^ 2) := by
  obtain ⟨C_pr, hC_pr, hpr⟩ := exists_prime_cross_le_split_mass_reserves
  refine ⟨C_pr + 532 + 28, by positivity, ?_⟩
  intro R M N hR hN2 hMN a w hw s t hs ht
  set aT : ℕ → ℝ := fun m => if m = 1 then 0 else a m with haT
  have hp := hpr hR hN2 hMN aT hw s t hs ht
  have hAT : (∑ m ∈ Icc 1 R, aT m ^ 2) ≤ ∑ m ∈ Icc 1 R, a m ^ 2 :=
    sum_le_sum fun m _ => by simp only [haT]; split_ifs <;> simp [sq_nonneg]
  have hET : primeAdjunctionMass R aT ≤ primeAdjunctionMass R a := by
    unfold primeAdjunctionMass
    refine sum_le_sum fun m hm => ?_
    simp only [haT]; split_ifs with h
    · subst h
      simp only [Nat.cast_one, Real.log_one, zero_add, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow, mul_zero]
      exact mul_nonneg (tameDifferent_nonneg 1) (sq_nonneg _)
    · exact le_rfl
  have hH0 : 0 ≤ 1 + Real.log R := by have := Real.log_natCast_nonneg R; linarith
  have hL : 0 < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hA0 : 0 ≤ ∑ m ∈ Icc 1 R, aT m ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  have hE0 : 0 ≤ primeAdjunctionMass R aT := primeAdjunctionMass_nonneg R aT
  have hB0 : 0 ≤ terminalPacketCost R M N := terminalPacketCost_nonneg R hMN
  have hEa : 0 ≤ primeAdjunctionMass R a := primeAdjunctionMass_nonneg R a
  change 2 * |⟪Matrix.toEuclideanLin (fullPrimeMatrix N)
      (∑ m ∈ Icc 1 R, aT m • normalizedRamanujanHorizonVector m N), w⟫| ≤ _
  have h1 : C_pr * (1 + Real.log R) * (∑ m ∈ Icc 1 R, aT m ^ 2) +
      532 * (1 + Real.log R) ^ 2 * primeAdjunctionMass R aT ≤
      (C_pr + 532 + 28) * ((1 + Real.log R) * (∑ m ∈ Icc 1 R, a m ^ 2) +
        (1 + Real.log R) ^ 2 * primeAdjunctionMass R a) := by
    have := mul_le_mul_of_nonneg_left hAT (mul_nonneg hC_pr.le hH0)
    have := mul_le_mul_of_nonneg_left hET (by positivity : (0 : ℝ) ≤ 532 * (1 + Real.log R) ^ 2)
    nlinarith [mul_nonneg hH0 (sum_nonneg fun m (_ : m ∈ Icc 1 R) => sq_nonneg (a m)),
      mul_nonneg (sq_nonneg (1 + Real.log R)) hEa]
  have h2 : C_pr * (1 + Real.log R) * (∑ m ∈ Icc 1 R, aT m ^ 2) +
      28 * (1 + Real.log R) * terminalPacketCost R M N * primeAdjunctionMass R aT ≤
      (C_pr + 532 + 28) * ((1 + Real.log R) * (∑ m ∈ Icc 1 R, a m ^ 2) +
        (1 + Real.log R) * terminalPacketCost R M N * primeAdjunctionMass R a) := by
    have := mul_le_mul_of_nonneg_left hAT (mul_nonneg hC_pr.le hH0)
    have := mul_le_mul_of_nonneg_left hET
      (by positivity : (0 : ℝ) ≤ 28 * (1 + Real.log R) * terminalPacketCost R M N)
    nlinarith [mul_nonneg hH0 (sum_nonneg fun m (_ : m ∈ Icc 1 R) => sq_nonneg (a m)),
      mul_nonneg (mul_nonneg hH0 hB0) hEa]
  have h1' := div_le_div_of_nonneg_right h1 (mul_pos hL hs).le
  have h2' := div_le_div_of_nonneg_right h2 (mul_pos hL ht).le
  have e1 : (C_pr * (1 + Real.log R) * ∑ m ∈ Icc 1 R, aT m ^ 2 +
      532 * (1 + Real.log R) ^ 2 * primeAdjunctionMass R aT) / (Real.log N * s) =
      (C_pr * (1 + Real.log R) * ∑ m ∈ Icc 1 R, aT m ^ 2 +
      532 * (1 + Real.log R) ^ 2 * primeAdjunctionMass R aT) / (Real.log N * s) := rfl
  linarith

/-- The budget of the six non-prime channels of the band–far cross (per unit `‖w‖²`), with
`A = Σ a²`, `G = Σ (1 + log m) a²`, `U = ‖u‖²`, `ρ ≥ ‖r₁‖²` the pole-mode residual and
`Sg₁ ≥ m/φ(m)`. -/
def bandFarChannelBudget (R N : ℕ) (c ρ Sg₁ A G U : ℝ) : ℝ :=
  ((1 + Real.log R) / Real.log N) ^ 2 * ρ * U +
    ((1 + Real.log R) * (1 + Real.log c) / Real.log N * G +
      c ^ 2 * (R : ℝ) ^ 5 / ((N : ℝ) ^ 2 * Real.log N) * A) +
    c ^ 2 * (24 + 780 * Sg₁ + 72 * (R : ℝ) ^ 15 / N) / Real.log N * U +
    c ^ 4 * (1 + Real.log c) / Real.log N * U +
    c ^ 3 * (R : ℝ) ^ 2 * (Real.log N / N) * U +
    c * (Sg₁ ^ 2 * (1 + Real.log c) / Real.log N + c ^ 5 / N +
      c ^ 3 * (R : ℝ) ^ 4 / (N * Real.log N)) * (1 + Real.log R) * G

/-- The six channel bounds against the channel budget. -/
theorem channel_sum_le_budget (R N : ℕ) (c ρ Sg₁ A G U : ℝ) {C_coh C_sep C_near C_jet : ℝ}
    (hcoh : 0 ≤ C_coh) (hsep : 0 ≤ C_sep) (hnear : 0 ≤ C_near) (hjet : 0 ≤ C_jet) (hc1 : 1 ≤ c)
    (hL : 0 < Real.log N) (hρ : 0 ≤ ρ) (hA : 0 ≤ A) (hG : 0 ≤ G) (hU : 0 ≤ U) (hSg : 0 ≤ Sg₁) :
    1296 * ((1 + Real.log R) / Real.log N) ^ 2 * ρ * U +
        C_coh * ((1 + Real.log R) * (1 + Real.log c) / Real.log N * G +
          c ^ 2 * (R : ℝ) ^ 5 / ((N : ℝ) ^ 2 * Real.log N) * A) +
        c ^ 2 * (24 + 780 * Sg₁ + 72 * (R : ℝ) ^ 15 / N) / Real.log N * U +
        C_sep * (c ^ 4 / Real.log N) * U +
        C_near * ((c ^ 4 * (1 + Real.log c) / Real.log N +
          c ^ 3 * (R : ℝ) ^ 2 * (Real.log N / N)) * U) +
        C_jet * c * (Sg₁ ^ 2 * (1 + Real.log c) / Real.log N + c ^ 5 / N +
          c ^ 3 * (R : ℝ) ^ 4 / (N * Real.log N)) * (1 + Real.log R) * G ≤
      (1296 + C_coh + C_sep + C_near + C_jet + 1) * bandFarChannelBudget R N c ρ Sg₁ A G U := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hlc := Real.log_nonneg hc1
  unfold bandFarChannelBudget
  generalize hT₁ : ((1 + Real.log R) / Real.log N) ^ 2 * ρ * U = T₁
  generalize hT₂ : (1 + Real.log R) * (1 + Real.log c) / Real.log N * G +
    c ^ 2 * (R : ℝ) ^ 5 / ((N : ℝ) ^ 2 * Real.log N) * A = T₂
  generalize hT₃ : c ^ 2 * (24 + 780 * Sg₁ + 72 * (R : ℝ) ^ 15 / N) / Real.log N * U = T₃
  generalize hT₆ : c * (Sg₁ ^ 2 * (1 + Real.log c) / Real.log N + c ^ 5 / N +
    c ^ 3 * (R : ℝ) ^ 4 / (N * Real.log N)) * (1 + Real.log R) * G = T₆
  have h1 : 0 ≤ T₁ := by rw [← hT₁]; positivity
  have h2 : 0 ≤ T₂ := by rw [← hT₂]; positivity
  have h3 : 0 ≤ T₃ := by rw [← hT₃]; positivity
  have h6 : 0 ≤ T₆ := by rw [← hT₆]; positivity
  have e6 : C_jet * c * (Sg₁ ^ 2 * (1 + Real.log c) / Real.log N + c ^ 5 / N +
      c ^ 3 * (R : ℝ) ^ 4 / (N * Real.log N)) * (1 + Real.log R) * G = C_jet * T₆ := by
    rw [← hT₆]; ring
  have e1 : 1296 * ((1 + Real.log R) / Real.log N) ^ 2 * ρ * U = 1296 * T₁ := by rw [← hT₁]; ring
  rw [e6, e1]
  generalize hT₄ : c ^ 4 * (1 + Real.log c) / Real.log N * U = T₄
  generalize hT₅ : c ^ 3 * (R : ℝ) ^ 2 * (Real.log N / N) * U = T₅
  have h4 : 0 ≤ T₄ := by rw [← hT₄]; positivity
  have h5 : 0 ≤ T₅ := by rw [← hT₅]; positivity
  have e5 : C_near * ((c ^ 4 * (1 + Real.log c) / Real.log N +
      c ^ 3 * (R : ℝ) ^ 2 * (Real.log N / N)) * U) = C_near * (T₄ + T₅) := by
    rw [← hT₄, ← hT₅]; ring
  rw [e5]
  have h4' : C_sep * (c ^ 4 / Real.log N) * U ≤ C_sep * T₄ := by
    rw [← hT₄, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ hsep
    apply mul_le_mul_of_nonneg_right _ hU
    exact div_le_div_of_nonneg_right (by nlinarith [pow_nonneg hc0.le 4]) hL.le
  have q1 := mul_nonneg (by positivity : (0 : ℝ) ≤ C_coh + C_sep + C_near + C_jet + 1) h1
  have q2 := mul_nonneg (by positivity : (0 : ℝ) ≤ 1296 + C_sep + C_near + C_jet + 1) h2
  have q3 := mul_nonneg (by positivity : (0 : ℝ) ≤ 1296 + C_coh + C_sep + C_near + C_jet) h3
  have q4 := mul_nonneg (by positivity : (0 : ℝ) ≤ 1296 + C_coh + C_jet + 1) h4
  have q5 := mul_nonneg (by positivity : (0 : ℝ) ≤ 1296 + C_coh + C_sep + C_jet + 1) h5
  have q6 := mul_nonneg (by positivity : (0 : ℝ) ≤ 1296 + C_coh + C_sep + C_near + 1) h6
  have e : (1296 + C_coh + C_sep + C_near + C_jet + 1) * (T₁ + T₂ + T₃ + T₄ + T₅ + T₆) =
      1296 * T₁ + C_coh * T₂ + T₃ + C_sep * T₄ + C_near * (T₄ + T₅) + C_jet * T₆ +
      ((C_coh + C_sep + C_near + C_jet + 1) * T₁ + (1296 + C_sep + C_near + C_jet + 1) * T₂ +
        (1296 + C_coh + C_sep + C_near + C_jet) * T₃ + (1296 + C_coh + C_jet + 1) * T₄ +
        (1296 + C_coh + C_sep + C_jet + 1) * T₅ + (1296 + C_coh + C_sep + C_near + 1) * T₆) := by
    ring
  rw [e]
  linarith

/-- **The band–far cross, channel by channel.** For a band `u = Σ_{m ≤ R} a_m v_m ⊥ v₁` and
`w ⊥ V_R`, with `u = a₁v₁ + ũ`: the pole mode pays through its residual `ρ`, the exact pole and
the jet's pole component cancel coherently, the center collar costs `max m/φ(m)`, the reduced jet
its divisor mean, and the upward channel splits into prefix rows `≤ M` and top rows `> M`. -/
theorem exists_band_far_cross_le_channels :
    ∃ C_pr C_up C_upT C_np : ℝ, 0 < C_pr ∧ 0 ≤ C_up ∧ 0 ≤ C_upT ∧ 0 ≤ C_np ∧
      ∀ {R M N : ℕ} {c ρ Sg₁ : ℝ}, 2 ≤ R → R ^ 6 ≤ N → 1 ≤ M → M ≤ N →
        18 * (1 + Real.log R) ≤ Real.log N → 1 ≤ c → 8 * c ≤ N → c ^ 4 ≤ N →
        ((R * R : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ N →
        ((R * R : ℕ) + 1 : ℝ) * (c * Real.exp 1 + 1) ≤ N →
        4 * (linearNearRowRadius c + 1) ^ 2 ≤ N →
        ⌈linearNearRowRadius c⌉₊ + 1 ≤ N → R * R ≤ N / (⌈linearNearRowRadius c⌉₊ + 1) →
        1 ≤ Sg₁ → (∀ m ∈ Icc 2 R, (m : ℝ) / m.totient ≤ Sg₁) →
        ‖poleModeResidual c N‖ ^ 2 ≤ ρ →
      ∀ a : ℕ → ℝ,
        (∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N) ∈ (conductorSubspace 1 N)ᗮ →
      ∀ {w : EuclideanSpace ℝ (PrimeHorizonIndex N)}, w ∈ (conductorSubspace R N)ᗮ →
      ∀ s₁ t₁ s₂ t₂ γ : ℝ, 0 < s₁ → 0 < t₁ → 0 < s₂ → 0 < t₂ → 0 < γ →
        2 * |⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
            (∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N), w⟫| ≤
          (C_pr * ((1 + Real.log R) * (∑ m ∈ Icc 1 R, a m ^ 2) +
                (1 + Real.log R) ^ 2 * primeAdjunctionMass R a) / (Real.log N * s₁) +
              C_pr * ((1 + Real.log R) * (∑ m ∈ Icc 1 R, a m ^ 2) +
                (1 + Real.log R) * terminalPacketCost R M N * primeAdjunctionMass R a) /
                  (Real.log N * t₁) +
              s₁ * (∑ n ∈ Icc 1 M, primeHorizonExtension w n ^ 2) +
              t₁ * (∑ n ∈ Ioc M N, primeHorizonExtension w n ^ 2)) +
            C_np * bandFarChannelBudget R N c ρ Sg₁ (∑ m ∈ Icc 1 R, a m ^ 2)
              (∑ m ∈ Icc 1 R, (1 + Real.log m) * a m ^ 2)
              (‖∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N‖ ^ 2) / γ +
            γ * ‖w‖ ^ 2 +
            (C_up * c ^ 2 * (1 + Real.log c) *
                ‖∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 / s₂ +
              s₂ * (∑ n ∈ Icc 1 M, primeHorizonExtension w n ^ 2)) +
            (C_upT * c ^ 2 * ((N : ℝ) / M) * (1 + Real.log c) / Real.log N *
                ‖∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 / t₂ +
              t₂ * (∑ n ∈ Ioc M N, primeHorizonExtension w n ^ 2)) := by
  obtain ⟨C_pr, hC_pr, hprime⟩ := exists_prime_channel_le
  obtain ⟨C_near, hC_near, hnear⟩ := exists_nearRemainder_channel_sq_le
  obtain ⟨C_jet, hC_jet, hjet⟩ := exists_reducedJet_channel_sq_le
  obtain ⟨C_coh, hC_coh, hcoh⟩ := exists_coherentPolePair_sq_le
    contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos
  obtain ⟨C_up, hC_up, hupP⟩ := exists_upward_prefix_channel_le
  obtain ⟨C_upT, hC_upT, hupS⟩ := exists_upward_top_channel_le
  obtain ⟨C_sep, hC_sep, hsepb⟩ := exists_sep_channel_sq_le
  refine ⟨C_pr, C_up, C_upT, 6 * (1296 + C_coh + C_sep + C_near + C_jet + 1), hC_pr, hC_up,
    hC_upT, by positivity, ?_⟩
  intro R M N c ρ Sg₁ hR hR6 hM1 hMN hlog hc1 h8 h4 hsize_near hsize_up hrad hceil hRK hSg1 hSg
    hρ a hu1 w hw s₁ t₁ s₂ t₂ γ hs₁ ht₁ hs₂ ht₂ hγ
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hN0 : (0 : ℝ) < N := by linarith
  have hN1 : 1 ≤ N := by
    have : (1 : ℝ) ≤ N := by linarith
    exact_mod_cast this
  have hN2 : 2 ≤ N := by
    have : (2 : ℝ) ≤ N := by linarith
    exact_mod_cast this
  have hRR : R * R ≤ N := by
    have hh := (Nat.pow_le_pow_right (by omega : 0 < R) (by norm_num : 2 ≤ 6)).trans hR6
    simpa only [sq] using hh
  have hRN : R ≤ N := (Nat.le_mul_self R).trans hRR
  have hL : 0 < Real.log N := by linarith [Real.log_natCast_nonneg R]
  have hw3 : c / N ≤ 1 / 3 := by rw [div_le_iff₀ hN0]; linarith
  have hw1 : c / N ≤ 1 := by linarith
  have hX := band_far_cross_eq (by omega : 1 ≤ R) hM1 hMN hc0 hN1 a hw
  have h₁ := poleMode_channel_sq_le hR hRR hlog hρ a hu1 w
  have h₂ : coherentPolePair c R N a w ^ 2 ≤
      (C_coh * ((1 + Real.log R) * (1 + Real.log c) / Real.log N *
          ∑ m ∈ Icc 1 R, (1 + Real.log m) * a m ^ 2 +
        c ^ 2 * (R : ℝ) ^ 5 / ((N : ℝ) ^ 2 * Real.log N) * ∑ m ∈ Icc 1 R, a m ^ 2)) * ‖w‖ ^ 2 := by
    have := hcoh hR hRN hL hc1 h8 h4 a hw
    unfold coherentPolePair poleFreeBand
    linarith
  have h₃ := collar_channel_sq_le hR hR6 hlog hc0 (by linarith : (0 : ℝ) ≤ Sg₁) hSg a w
  have h₄ := hsepb hR hR6 hlog hc0 a w
  have h₅ := hnear hR hRR hlog hc1 hw3 hsize_near a w
  have h₆ := hjet hR hlog hc1 hw1 hrad hceil hRK hSg1 hSg a w
  have hPr := hprime hR hN2 hMN a hw hs₁ ht₁
  have hUP := hupP hR hRR hlog hc1 hw3 hsize_up hMN a w hs₂
  have hUS := hupS hR hRR hlog hc1 hw3 hsize_up hM1 a w ht₂
  have hlc := Real.log_nonneg hc1
  have hlR := Real.log_natCast_nonneg R
  have hU0 : 0 ≤ ‖∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 := sq_nonneg _
  have hA0 : 0 ≤ ∑ m ∈ Icc 1 R, a m ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  have hG0 : 0 ≤ ∑ m ∈ Icc 1 R, (1 + Real.log m) * a m ^ 2 :=
    sum_nonneg fun m _ => mul_nonneg (by linarith [Real.log_natCast_nonneg m]) (sq_nonneg _)
  have hρ0 : 0 ≤ ρ := le_trans (sq_nonneg _) hρ
  have harith := band_far_cross_arith hX hPr h₁ h₂ h₃ h₄ h₅ h₆ (by positivity) (by positivity)
    (by positivity) (by positivity) (by positivity) (by positivity) hUP hUS hγ
  have hsum := channel_sum_le_budget R N c ρ Sg₁ (∑ m ∈ Icc 1 R, a m ^ 2)
    (∑ m ∈ Icc 1 R, (1 + Real.log m) * a m ^ 2)
    (‖∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N‖ ^ 2) hC_coh hC_sep hC_near hC_jet
    hc1 hL hρ0 hA0 hG0 hU0 (by linarith)
  have hsix := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 6))
    hγ.le
  rw [show ∀ x y : ℝ, 6 * (x * y) = 6 * x * y from fun x y => by ring] at hsix
  linarith

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
