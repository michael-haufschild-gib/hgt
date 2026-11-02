import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.SharpenedMidBandAndCrossBounds
import GaloisForLFunctions.RHTower.NicolasTotientLandau
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.ThePrimeCrossOfAPrefixAndATopIsADirichletConvolution
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheFlipThresholdGrowsLikeAPowerOfThePrime

/-!
# The near-Gram form of a packet costs its divisor mean

The near Gram kernel `K₂ᵦ(n, j) = A(|log j − log n| N/c)/∫φ²` (`A` the profile autocorrelation)
is the off-diagonal part of the atomic Gram matrix `Γ = I + K₂ᵦ`, `Γ(n, j) = ⟨g_n, g_j⟩/∫g²`
(`sum_bumpCorr_atomDilate_row`). Since `Γ` is a Gram matrix with frame bound `λ = 1 + 2ec`,
`‖K₂ᵦ y‖² ≤ (λ − 2) ⟨Γ y, y⟩ + ‖y‖²` (`sum_nearGram_sq_le_gram`): the operator costs `c` times
the form, not `c²`.

On a packet `u = Σ_m a_m v_m` the form splits, after linearization, into the shifted-mode
mean `Σ_m a_m² φ(m)⁻¹ Σ_h c_m(h) W_h` and oscillations (`midBandLinearizedSum_eq_mean_add_osc`).
Expanding `c_m(h) = Σ_{d ∣ m} μ(m/d) d [d ∣ h]`, each progression carries the mean `(1/d) Σ W`
up to the variation of `W` (Abel), and `Σ_{d ∣ m} μ(m/d) = 0` for `m ≥ 2`
(`abs_sum_ramanujanLagCoefficient_mul_le`). The weights `W_h` vary by `O(1 + log c)`
(`exists_nearWeightMass_variation_le`), so for `a 1 = 0` the mean costs
`O((1 + log c) σ(m)/φ(m))` per unit mass (`exists_midBand_mean_sum_le_divisor_mean`) and
`|⟨K₂ᵦ u, u⟩| ≲ (c⁵/N + (1 + log c) Sg/log N + c³R⁴/(N log N)) ‖u‖²`
(`exists_nearGram_packet_form_le`), `Sg ≥ σ(m)/φ(m)`.
-/

set_option autoImplicit false
noncomputable section

open Finset ArithmeticFunction

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open BezoutValuationIncidence RenormalizedArithmeticPotentialTheory CompletedArithmeticForms
  RenormalizedArithmeticPotentialTheory.CompletedShell
  SpacingScaleHarmonicAnalysis

/-- Abel's identity on `Icc 1 H`: `Σ e_h W_h = E_H W_H − Σ_{h<H} E_h (W_{h+1} − W_h)`. -/
theorem sum_Icc_mul_eq_abel (e W : ℕ → ℝ) (H : ℕ) :
    (∑ h ∈ Icc 1 H, e h * W h) =
      (∑ h ∈ Icc 1 H, e h) * W H -
        ∑ h ∈ Ico 1 H, (∑ i ∈ Icc 1 h, e i) * (W (h + 1) - W h) := by
  induction H with
  | zero => simp
  | succ H ih =>
    rw [sum_Icc_succ_top (by omega), ih, sum_Icc_succ_top (by omega)]
    rcases Nat.eq_zero_or_pos H with rfl | hH
    · simp
    rw [sum_Ico_succ_top (by omega)]
    ring

/-- With partial sums of `e` bounded by `1`, `|Σ e_h W_h| ≤ |W_H| + Σ |W_{h+1} − W_h|`. -/
theorem abs_sum_Icc_mul_le_of_partial (e W : ℕ → ℝ) (H : ℕ)
    (he : ∀ y ≤ H, |∑ h ∈ Icc 1 y, e h| ≤ 1) :
    |∑ h ∈ Icc 1 H, e h * W h| ≤
      |W H| + ∑ h ∈ Ico 1 H, |W (h + 1) - W h| := by
  rw [sum_Icc_mul_eq_abel]
  refine (abs_sub _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul]
    calc _ ≤ 1 * |W H| := mul_le_mul_of_nonneg_right (he H le_rfl) (abs_nonneg _)
      _ = _ := one_mul _
  · refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun h hh => ?_)
    rw [abs_mul]
    have := he h (by have := (mem_Ico.mp hh).2; omega)
    calc _ ≤ 1 * |W (h + 1) - W h| := mul_le_mul_of_nonneg_right this (abs_nonneg _)
      _ = _ := one_mul _

/-- **Divisibility against the mean.** `|Σ_{h ≤ H, d ∣ h} W_h − (1/d) Σ_{h ≤ H} W_h| ≤
|W_H| + Σ |W_{h+1} − W_h|`. -/
theorem abs_sum_Icc_dvd_sub_mean_le (W : ℕ → ℝ) {d : ℕ} (hd : 0 < d) (H : ℕ) :
    |(∑ h ∈ Icc 1 H, (if d ∣ h then W h else 0)) - (1 / (d : ℝ)) * ∑ h ∈ Icc 1 H, W h| ≤
      |W H| + ∑ h ∈ Ico 1 H, |W (h + 1) - W h| := by
  have he : ∀ y ≤ H, |∑ h ∈ Icc 1 y, ((if d ∣ h then (1 : ℝ) else 0) - 1 / (d : ℝ))| ≤ 1 := by
    intro y _
    rw [sum_sub_distrib, sum_const, Nat.card_Icc, add_tsub_cancel_right, ← sum_filter,
      sum_const, nsmul_eq_mul, mul_one, nsmul_eq_mul]
    have hcard : (((Icc 1 y).filter (fun h => d ∣ h)).card : ℝ) = (y / d : ℕ) := by
      rw [show (Icc 1 y : Finset ℕ) = Ioc 0 y by ext x; simp only [mem_Icc, mem_Ioc]; omega,
        Nat.Ioc_filter_dvd_card_eq_div]
    rw [hcard]
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
    have h1 : ((y / d : ℕ) : ℝ) ≤ (y : ℝ) / d := Nat.cast_div_le
    have h2 : (y : ℝ) / d < ((y / d : ℕ) : ℝ) + 1 := by
      rw [div_lt_iff₀ hd0]
      have := Nat.lt_div_mul_add hd (a := y)
      have : (y : ℝ) < ((y / d : ℕ) : ℝ) * d + d := by exact_mod_cast this
      linarith
    rw [abs_le]; constructor
    · have : (y : ℝ) * (1 / d) = y / d := by ring
      linarith
    · have : (y : ℝ) * (1 / d) = y / d := by ring
      linarith
  have h := abs_sum_Icc_mul_le_of_partial _ W H he
  have hid : (∑ h ∈ Icc 1 H, (if d ∣ h then W h else 0)) - (1 / (d : ℝ)) * ∑ h ∈ Icc 1 H, W h =
      ∑ h ∈ Icc 1 H, ((if d ∣ h then (1 : ℝ) else 0) - 1 / (d : ℝ)) * W h := by
    rw [mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun h _ => ?_
    split_ifs <;> ring
  rw [hid]; exact h

/-- **The Ramanujan mean of a slowly varying weight.** For a conductor `m ≥ 2`,
`|Σ_{h ≤ H} c_m(h) W_h| ≤ σ(m) (|W_H| + Σ |W_{h+1} − W_h|)`: the progressions `d ∣ h` carry the
mean `(1/d) Σ W`, which the Möbius sum `Σ_{d ∣ m} μ(m/d) = 0` annihilates. -/
theorem abs_sum_ramanujanLagCoefficient_mul_le {m : ℕ} (hm : 2 ≤ m) (W : ℕ → ℝ) (H : ℕ) :
    |∑ h ∈ Icc 1 H, ramanujanLagCoefficient m h * W h| ≤
      (ArithmeticFunction.sigma 1 m : ℝ) * (|W H| + ∑ h ∈ Ico 1 H, |W (h + 1) - W h|) := by
  set V := |W H| + ∑ h ∈ Ico 1 H, |W (h + 1) - W h| with hV
  set S := ∑ h ∈ Icc 1 H, W h with hS
  have hm0 : m ≠ 0 := by omega
  -- expand the Ramanujan sum over divisors
  have hexp : (∑ h ∈ Icc 1 H, ramanujanLagCoefficient m h * W h) =
      ∑ d ∈ m.divisors, moebiusReal (m / d) * d *
        ∑ h ∈ Icc 1 H, (if d ∣ h then W h else 0) := by
    simp only [ramanujanLagCoefficient, sum_mul]
    rw [sum_comm]
    refine sum_congr rfl fun d _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun h _ => ?_
    split_ifs <;> ring
  have hmu : (∑ d ∈ m.divisors, moebiusReal (m / d)) = 0 := by
    rw [Nat.sum_div_divisors m (fun k => moebiusReal k)]
    have h := congrArg (fun f : ArithmeticFunction ℝ => f m)
      (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℝ))
    simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply_ne
      (show m ≠ 1 by omega)] at h
    simpa only [moebiusReal, ArithmeticFunction.intCoe_apply] using h
  have hsplit : (∑ d ∈ m.divisors, moebiusReal (m / d) * d *
        ∑ h ∈ Icc 1 H, (if d ∣ h then W h else 0)) =
      (∑ d ∈ m.divisors, moebiusReal (m / d)) * S +
        ∑ d ∈ m.divisors, moebiusReal (m / d) * d *
          ((∑ h ∈ Icc 1 H, (if d ∣ h then W h else 0)) - (1 / (d : ℝ)) * S) := by
    rw [sum_mul, ← sum_add_distrib]
    refine sum_congr rfl fun d hd => ?_
    have hd0 : (d : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
    field_simp
    ring
  rw [hexp, hsplit, hmu, zero_mul, zero_add]
  calc _ ≤ ∑ d ∈ m.divisors, |moebiusReal (m / d) * d *
        ((∑ h ∈ Icc 1 H, (if d ∣ h then W h else 0)) - (1 / (d : ℝ)) * S)| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ m.divisors, (d : ℝ) * V := sum_le_sum fun d hd => by
        have hd0 := Nat.pos_of_mem_divisors hd
        rw [abs_mul, abs_mul, Nat.abs_cast]
        have hmu1 : |moebiusReal (m / d)| ≤ 1 := by
          unfold moebiusReal; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
        have := abs_sum_Icc_dvd_sub_mean_le W hd0 H
        calc |moebiusReal (m / d)| * d * _ ≤ 1 * d * V :=
              mul_le_mul (mul_le_mul_of_nonneg_right hmu1 (Nat.cast_nonneg _)) this
                (abs_nonneg _) (by positivity)
          _ = d * V := by ring
    _ = (ArithmeticFunction.sigma 1 m : ℝ) * V := by
        rw [← sum_mul, ArithmeticFunction.sigma_one_apply]; push_cast; ring

/-! ### The linearized near weights vary by `O(1 + log c)` -/

private theorem log_two_mul_linearNearRowRadius_le' {c : ℝ} (hc1 : 1 ≤ c) :
    Real.log (2 * (linearNearRowRadius c + 1)) + 3 ≤ 10 * (1 + Real.log c) := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have he2 : Real.exp 2 ≤ 8 := by
    have h1 : Real.exp 1 ≤ 14 / 5 := by linarith [Real.exp_one_lt_d9]
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith only [h1, h2, Real.exp_pos 1]
  have hlin : 2 * (linearNearRowRadius c + 1) ≤ 34 * c := by
    unfold linearNearRowRadius
    nlinarith only [hc1, he2]
  have hlog34 : Real.log 34 ≤ 6 := by
    have he1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have he6 : (34 : ℝ) ≤ Real.exp 6 := by
      have hpow : (2 : ℝ) ^ 6 ≤ (Real.exp 1) ^ 6 := pow_le_pow_left₀ (by norm_num) he1 6
      rw [← Real.exp_nat_mul] at hpow
      norm_num at hpow
      linarith only [hpow]
    exact (Real.log_le_log (by norm_num) he6).trans_eq (Real.log_exp 6)
  have hlog_le : Real.log (2 * (linearNearRowRadius c + 1)) ≤ 6 + Real.log c := by
    calc
      Real.log (2 * (linearNearRowRadius c + 1)) ≤ Real.log (34 * c) :=
        Real.log_le_log (by unfold linearNearRowRadius; positivity) hlin
      _ = Real.log 34 + Real.log c := Real.log_mul (by norm_num) hc0.ne'
      _ ≤ 6 + Real.log c := by linarith only [hlog34]
  have hlc0 : 0 ≤ Real.log c := Real.log_nonneg hc1
  linarith only [hlog_le, hlc0]

/-- The near weight mass at shift `h`: `W_h = Σ_{N/T < n ≤ N − h} (1/n) A(N h/(c n))`. -/
def nearWeightMass (φ : ℝ → ℝ) (c : ℝ) (N h : ℕ) : ℝ :=
  ∑ n ∈ Ioc ⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ (N - h), midBandLinearizedWeight φ c N h n

private theorem sum_Ioc_top_one_div_le {N : ℕ} (hN : 1 ≤ N) {c : ℝ} (hc1 : 1 ≤ c) (h : ℕ) :
    (∑ n ∈ Ioc ⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ (N - h), 1 / (n : ℝ)) ≤
      10 * (1 + Real.log c) := by
  set T := linearNearRowRadius c + 1
  have hT1 : 1 ≤ T := by
    have : 0 ≤ linearNearRowRadius c := by unfold linearNearRowRadius; positivity
    simp only [T]; linarith
  have hT0 : 0 < T := zero_lt_one.trans_le hT1
  have hsub : Ioc ⌊(N : ℝ) / T⌋₊ (N - h) ⊆ (Icc 1 N).filter (fun n : ℕ => (N : ℝ) / (n : ℝ) < T) := by
    intro n hn
    obtain ⟨hn_lo, hn_hi⟩ := mem_Ioc.mp hn
    have hn1 : 1 ≤ n := by omega
    have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn1
    have hfloor : (N : ℝ) / T < (⌊(N : ℝ) / T⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    have hn_ge : (⌊(N : ℝ) / T⌋₊ : ℝ) + 1 ≤ n := by exact_mod_cast hn_lo
    refine mem_filter.mpr ⟨mem_Icc.mpr ⟨hn1, by omega⟩, ?_⟩
    rw [div_lt_iff₀ hn0]
    have := (div_lt_iff₀ hT0).mp (hfloor.trans_le hn_ge)
    linarith
  have hlogT := log_two_mul_linearNearRowRadius_le' hc1
  calc _ ≤ ∑ n ∈ (Icc 1 N).filter (fun n : ℕ => (N : ℝ) / (n : ℝ) < T), 1 / (n : ℝ) :=
        sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    _ ≤ 1 + Real.log (2 * T) := HTGeometry.harmonic_quotient_tail_le hN hT1
    _ ≤ 10 * (1 + Real.log c) := by linarith

/-- `|W_h| ≤ 10 ∫φ² (1 + log c)`. -/
theorem abs_nearWeightMass_le {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ t, t ∉ Set.Icc 0 1 → φ t = 0) {N : ℕ} (hN : 1 ≤ N) {c : ℝ} (hc1 : 1 ≤ c)
    (h : ℕ) : |nearWeightMass φ c N h| ≤ 10 * (∫ t, φ t ^ 2) * (1 + Real.log c) := by
  have hG_le : ∀ t, |shellAutocorr φ t| ≤ ∫ t, φ t ^ 2 := abs_shellAutocorr_le hφ hsupp
  unfold nearWeightMass
  calc _ ≤ ∑ n ∈ Ioc ⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ (N - h),
        (1 / (n : ℝ)) * ∫ t, φ t ^ 2 := by
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun n hn => ?_)
        have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (by have := (mem_Ioc.mp hn).1; omega)
        unfold midBandLinearizedWeight
        rw [abs_mul, abs_of_pos (one_div_pos.mpr hn0)]
        exact mul_le_mul_of_nonneg_left (hG_le _) (by positivity)
    _ = (∑ n ∈ Ioc ⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ (N - h), 1 / (n : ℝ)) *
        ∫ t, φ t ^ 2 := (sum_mul ..).symm
    _ ≤ 10 * (1 + Real.log c) * ∫ t, φ t ^ 2 :=
        mul_le_mul_of_nonneg_right (sum_Ioc_top_one_div_le hN hc1 h)
          (MeasureTheory.integral_nonneg fun _ => sq_nonneg _)
    _ = _ := by ring

/-- Samples of a Lipschitz profile vanishing beyond `1` at step `δ` have total variation `≤ K`. -/
private theorem sum_Ico_abs_sub_samples_le {A : ℝ → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hA : ∀ x y, |A x - A y| ≤ K * |x - y|) (hA1 : ∀ x, 1 ≤ x → A x = 0) {δ : ℝ}
    (hδ : 0 < δ) (H : ℕ) :
    (∑ h ∈ Ico 1 H, |A (δ * (h + 1 : ℕ)) - A (δ * h)|) ≤ K := by
  classical
  have hterm : ∀ h ∈ Ico 1 H, |A (δ * (h + 1 : ℕ)) - A (δ * h)| ≤
      if δ * h < 1 then K * δ else 0 := by
    intro h _
    split_ifs with hlt
    · calc _ ≤ K * |δ * (h + 1 : ℕ) - δ * h| := hA _ _
        _ = K * δ := by push_cast; rw [show δ * ((h : ℝ) + 1) - δ * h = δ by ring, abs_of_pos hδ]
    · push Not at hlt
      rw [hA1 _ hlt, hA1 _ (by push_cast; nlinarith), sub_zero, abs_zero]
  refine (sum_le_sum hterm).trans ?_
  rw [← sum_filter, sum_const, nsmul_eq_mul]
  have hcard : (((Ico 1 H).filter (fun h : ℕ => δ * h < 1)).card : ℝ) ≤ 1 / δ := by
    have hsub : (Ico 1 H).filter (fun h : ℕ => δ * h < 1) ⊆ Icc 1 ⌊1 / δ⌋₊ := by
      intro h hh
      obtain ⟨hh1, hlt⟩ := mem_filter.mp hh
      refine mem_Icc.mpr ⟨(mem_Ico.mp hh1).1, Nat.le_floor ?_⟩
      rw [le_div_iff₀ hδ]; linarith
    calc _ ≤ ((Icc 1 ⌊1 / δ⌋₊).card : ℝ) := by exact_mod_cast card_le_card hsub
      _ = (⌊1 / δ⌋₊ : ℝ) := by rw [Nat.card_Icc]; simp
      _ ≤ 1 / δ := Nat.floor_le (by positivity)
  calc _ ≤ (1 / δ) * (K * δ) := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = K := by field_simp

/-- `W_h` as a sum over all top rows with the cutoff `n ≤ N − h` as an indicator. -/
private theorem nearWeightMass_eq_indicator (φ : ℝ → ℝ) (c : ℝ) (N h : ℕ) :
    nearWeightMass φ c N h =
      ∑ n ∈ Ioc ⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ N,
        (if n ≤ N - h then midBandLinearizedWeight φ c N h n else 0) := by
  unfold nearWeightMass
  rw [← sum_filter]
  congr 1
  ext n; simp only [mem_Ioc, mem_filter]; omega

/-- **The near weight masses vary by `O(1 + log c)`.** -/
theorem exists_nearWeightMass_variation_le {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ t, t ∉ Set.Icc 0 1 → φ t = 0) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ {N : ℕ} {c : ℝ}, 1 ≤ N → 1 ≤ c →
      2 * ⌊linearNearRowRadius c⌋₊ ≤ N →
      |nearWeightMass φ c N ⌊linearNearRowRadius c⌋₊| +
          ∑ h ∈ Ico 1 ⌊linearNearRowRadius c⌋₊,
            |nearWeightMass φ c N (h + 1) - nearWeightMass φ c N h| ≤
        C₀ * (1 + Real.log c) := by
  obtain ⟨K, hK⟩ := exists_lipschitz_shellAutocorr hφ hsupp
  set M2 := ∫ t, φ t ^ 2 with hM2
  have hM20 : 0 ≤ M2 := MeasureTheory.integral_nonneg fun _ => sq_nonneg _
  have hG_le : ∀ t, |shellAutocorr φ t| ≤ M2 := abs_shellAutocorr_le hφ hsupp
  refine ⟨12 * M2 + 10 * K, by positivity, ?_⟩
  intro N c hN hc1 hHN
  set H := ⌊linearNearRowRadius c⌋₊ with hH
  set L := ⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ with hL
  have hlc0 : 0 ≤ Real.log c := Real.log_nonneg hc1
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hA : ∀ x y, |shellAutocorr φ x - shellAutocorr φ y| ≤ (K : ℝ) * |x - y| := by
    intro x y
    have := hK.dist_le_mul x y
    simpa only [Real.dist_eq] using this
  have hA1 : ∀ x, 1 ≤ x → shellAutocorr φ x = 0 := fun x hx =>
    shellAutocorr_eq_zero_of_one_le hφ hsupp hx
  -- per-shift variation
  have hstep : ∀ h ∈ Ico 1 H, |nearWeightMass φ c N (h + 1) - nearWeightMass φ c N h| ≤
      (∑ n ∈ Ioc L N, |midBandLinearizedWeight φ c N (h + 1) n -
          midBandLinearizedWeight φ c N h n|) + 2 * M2 / N := by
    intro h hh
    have hhH := (mem_Ico.mp hh).2
    rw [nearWeightMass_eq_indicator, nearWeightMass_eq_indicator, ← sum_sub_distrib]
    calc _ ≤ ∑ n ∈ Ioc L N, |(if n ≤ N - (h + 1) then midBandLinearizedWeight φ c N (h + 1) n
            else 0) - (if n ≤ N - h then midBandLinearizedWeight φ c N h n else 0)| :=
          abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ Ioc L N, (|midBandLinearizedWeight φ c N (h + 1) n -
            midBandLinearizedWeight φ c N h n| +
            (if n = N - h then |midBandLinearizedWeight φ c N h n| else 0)) := by
          refine sum_le_sum fun n hn => ?_
          by_cases h1 : n ≤ N - (h + 1)
          · have h2 : n ≤ N - h := by omega
            rw [if_pos h1, if_pos h2, if_neg (by omega)]; linarith
          · by_cases h2 : n ≤ N - h
            · have h3 : n = N - h := by omega
              rw [if_neg h1, if_pos h2, if_pos h3, zero_sub, abs_neg]
              linarith [abs_nonneg (midBandLinearizedWeight φ c N (h + 1) n -
                midBandLinearizedWeight φ c N h n)]
            · rw [if_neg h1, if_neg h2, sub_zero, abs_zero]
              have : (0 : ℝ) ≤ if n = N - h then |midBandLinearizedWeight φ c N h n| else 0 := by
                split_ifs <;> positivity
              linarith [abs_nonneg (midBandLinearizedWeight φ c N (h + 1) n -
                midBandLinearizedWeight φ c N h n)]
      _ ≤ _ := by
          rw [sum_add_distrib]
          refine add_le_add le_rfl ?_
          rw [sum_ite_eq']
          split_ifs with hmem
          · have hn0 : (0 : ℝ) < (N - h : ℕ) := by
              have := (mem_Ioc.mp hmem).1; exact_mod_cast (show 0 < N - h by omega)
            unfold midBandLinearizedWeight
            rw [abs_mul, abs_of_pos (one_div_pos.mpr hn0)]
            have hhalf : (N : ℝ) / 2 ≤ (N - h : ℕ) := by
              rw [Nat.cast_sub (by omega)]
              have : (h : ℝ) ≤ N / 2 := by
                have : 2 * h ≤ N := by omega
                have : (2 * h : ℝ) ≤ N := by exact_mod_cast this
                linarith
              linarith
            calc 1 / ((N - h : ℕ) : ℝ) * |shellAutocorr φ _| ≤ 1 / ((N - h : ℕ) : ℝ) * M2 :=
                  mul_le_mul_of_nonneg_left (hG_le _) (by positivity)
              _ ≤ 1 / ((N : ℝ) / 2) * M2 := mul_le_mul_of_nonneg_right
                  (one_div_le_one_div_of_le (by positivity) hhalf) hM20
              _ = 2 * M2 / N := by field_simp
          · positivity
  -- per-row variation
  have hrow : ∀ n ∈ Ioc L N, (∑ h ∈ Ico 1 H, |midBandLinearizedWeight φ c N (h + 1) n -
      midBandLinearizedWeight φ c N h n|) ≤ (K : ℝ) * (1 / (n : ℝ)) := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by have := (mem_Ioc.mp hn).1; omega)
    have hδ : 0 < (N : ℝ) / c * (1 / n) := by positivity
    have hsam := sum_Ico_abs_sub_samples_le (K := (K : ℝ)) K.coe_nonneg hA hA1 hδ H
    unfold midBandLinearizedWeight
    calc _ = ∑ h ∈ Ico 1 H, (1 / (n : ℝ)) * |shellAutocorr φ ((N : ℝ) / c * (1 / n) *
          ((h + 1 : ℕ) : ℝ)) - shellAutocorr φ ((N : ℝ) / c * (1 / n) * h)| := by
          refine sum_congr rfl fun h _ => ?_
          rw [← mul_sub, abs_mul, abs_of_pos (one_div_pos.mpr hn0)]
          congr 3 <;> push_cast <;> ring_nf
      _ = (1 / (n : ℝ)) * ∑ h ∈ Ico 1 H, |shellAutocorr φ ((N : ℝ) / c * (1 / n) *
          ((h + 1 : ℕ) : ℝ)) - shellAutocorr φ ((N : ℝ) / c * (1 / n) * h)| := (mul_sum ..).symm
      _ ≤ (1 / (n : ℝ)) * K := mul_le_mul_of_nonneg_left hsam (by positivity)
      _ = _ := by ring
  have hTV : (∑ h ∈ Ico 1 H, |nearWeightMass φ c N (h + 1) - nearWeightMass φ c N h|) ≤
      10 * K * (1 + Real.log c) + M2 := by
    calc _ ≤ ∑ h ∈ Ico 1 H, ((∑ n ∈ Ioc L N, |midBandLinearizedWeight φ c N (h + 1) n -
          midBandLinearizedWeight φ c N h n|) + 2 * M2 / N) := sum_le_sum hstep
      _ = (∑ n ∈ Ioc L N, ∑ h ∈ Ico 1 H, |midBandLinearizedWeight φ c N (h + 1) n -
          midBandLinearizedWeight φ c N h n|) + (H - 1 : ℕ) * (2 * M2 / N) := by
          rw [sum_add_distrib, sum_comm, sum_const, Nat.card_Ico, nsmul_eq_mul]
      _ ≤ (∑ n ∈ Ioc L N, (K : ℝ) * (1 / (n : ℝ))) + M2 := by
          refine add_le_add (sum_le_sum hrow) ?_
          have : ((H - 1 : ℕ) : ℝ) * 2 ≤ N := by
            have : 2 * (H - 1) ≤ N := by omega
            exact_mod_cast (show (H - 1) * 2 ≤ N by omega)
          calc ((H - 1 : ℕ) : ℝ) * (2 * M2 / N) = ((H - 1 : ℕ) : ℝ) * 2 / N * M2 := by ring
            _ ≤ 1 * M2 := mul_le_mul_of_nonneg_right (by rw [div_le_one hN0]; exact this) hM20
            _ = M2 := one_mul _
      _ ≤ 10 * K * (1 + Real.log c) + M2 := by
          rw [← mul_sum]
          have := sum_Ioc_top_one_div_le hN hc1 0
          rw [Nat.sub_zero] at this
          have hK0 : (0 : ℝ) ≤ K := K.coe_nonneg
          nlinarith
  have hW := abs_nearWeightMass_le hφ hsupp hN hc1 H
  rw [← hM2] at hW
  have : M2 ≤ M2 * (1 + Real.log c) := le_mul_of_one_le_right hM20 (by linarith)
  nlinarith

/-- **The near-Gram mean of a packet without the pole conductor.** For `a 1 = 0`, the diagonal
(mean) part of the near-Gram form costs `C (1 + log c) max σ(m)/φ(m)` per unit mass. -/
theorem exists_midBand_mean_sum_le_divisor_mean {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ t, t ∉ Set.Icc 0 1 → φ t = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {R₂ N : ℕ} {c : ℝ}, 2 ≤ R₂ → R₂ * R₂ ≤ N →
      18 * (1 + Real.log R₂) ≤ Real.log N → 1 ≤ c → 2 * ⌊linearNearRowRadius c⌋₊ ≤ N →
      ∀ {a : ℕ → ℝ}, a 1 = 0 → ∀ {Sg : ℝ},
        (∀ m ∈ Icc 2 R₂, (ArithmeticFunction.sigma 1 m : ℝ) / m.totient ≤ Sg) →
        |midBandMeanSum φ R₂ N c a| ≤ C * (1 + Real.log c) * Sg *
          ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 := by
  obtain ⟨C₀, hC₀, hV⟩ := exists_nearWeightMass_variation_le hφ hsupp
  refine ⟨2 * C₀, by positivity, ?_⟩
  intro R₂ N c hR₂ hR₂N hlog hc1 hHN a ha1 Sg hSg
  have hN : 1 ≤ N := le_trans (by nlinarith) hR₂N
  set H := ⌊linearNearRowRadius c⌋₊ with hH
  set V := |nearWeightMass φ c N H| +
    ∑ h ∈ Ico 1 H, |nearWeightMass φ c N (h + 1) - nearWeightMass φ c N h| with hVdef
  have hVle := hV hN hc1 hHN
  rw [← hH, ← hVdef] at hVle
  have hV0 : 0 ≤ V := by positivity
  have hSg0 : 0 ≤ Sg := by
    have h2 := hSg 2 (mem_Icc.mpr ⟨le_rfl, hR₂⟩)
    exact le_trans (by positivity) h2
  have hswap : midBandMeanSum φ R₂ N c a =
      ∑ m ∈ Icc 1 R₂, (a m ^ 2 / m.totient) *
        ∑ h ∈ Icc 1 H, ramanujanLagCoefficient m h * nearWeightMass φ c N h := by
    unfold midBandMeanSum
    rw [sum_comm]
    refine sum_congr rfl fun m _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun h _ => ?_
    unfold nearWeightMass
    ring
  have hriesz := (half_and_three_halves_riesz_of_log_le hR₂ hR₂N hlog a).1
  rw [hswap]
  calc _ ≤ ∑ m ∈ Icc 1 R₂, |(a m ^ 2 / m.totient) *
        ∑ h ∈ Icc 1 H, ramanujanLagCoefficient m h * nearWeightMass φ c N h| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ m ∈ Icc 1 R₂, a m ^ 2 * (Sg * V) := sum_le_sum fun m hm => by
        obtain ⟨hm1, hmR⟩ := mem_Icc.mp hm
        rcases eq_or_lt_of_le hm1 with h1 | h2
        · subst h1; rw [ha1]; simp
        · have hφ0 : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega)
          have hmean := abs_sum_ramanujanLagCoefficient_mul_le (show 2 ≤ m by omega)
            (nearWeightMass φ c N) H
          rw [← hVdef] at hmean
          have hσ := hSg m (mem_Icc.mpr ⟨by omega, hmR⟩)
          rw [abs_mul, abs_of_nonneg (by positivity)]
          calc a m ^ 2 / m.totient * |∑ h ∈ Icc 1 H, ramanujanLagCoefficient m h *
                nearWeightMass φ c N h|
              ≤ a m ^ 2 / m.totient * ((ArithmeticFunction.sigma 1 m : ℝ) * V) :=
                mul_le_mul_of_nonneg_left hmean (by positivity)
            _ = a m ^ 2 * (((ArithmeticFunction.sigma 1 m : ℝ) / m.totient) * V) := by ring
            _ ≤ a m ^ 2 * (Sg * V) := mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right hσ hV0) (sq_nonneg _)
    _ = (Sg * V) * ∑ m ∈ Icc 1 R₂, a m ^ 2 := by rw [mul_sum]; exact sum_congr rfl fun _ _ => by ring
    _ ≤ (Sg * (C₀ * (1 + Real.log c))) *
          (2 * ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖ ^ 2) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hVle hSg0) (by linarith)
          (sum_nonneg fun _ _ => sq_nonneg _)
          (mul_nonneg hSg0 (mul_nonneg hC₀ (by linarith [Real.log_nonneg hc1])))
    _ = _ := by ring

/-! ### The near Gram operator is controlled by its quadratic form -/

/-- The near Gram operator `(K₂ᵦ y)(n) = Σ_{j near n} A(|log j − log n|/(c/N))/∫φ² · y_j`. -/
def nearGram (φ : ℝ → ℝ) (c : ℝ) (N : ℕ) (y : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ nearRowIndices c N n,
    shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) / (∫ t, φ t ^ 2) * y j

/-- Rows of the atomic Gram matrix: `Σ_j y_j ⟨g_n, g_j⟩ = G (y_n + (K₂ᵦ y)(n))`. -/
theorem sum_bumpCorr_atomDilate_row {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ t, t ∉ Set.Icc 0 1 → φ t = 0) (hM : 0 < ∫ t, φ t ^ 2) {c : ℝ} {N : ℕ}
    (hc : 0 < c) (hN : 0 < N) (y : ℕ → ℝ) {n : ℕ} (hn : n ∈ Icc 1 N) :
    (∑ j ∈ Icc 1 N, y j * bumpCorr (atomDilate φ (c / N)) (Real.log n - Real.log j)) =
      (∫ u, atomDilate φ (c / N) u ^ 2) * (y n + nearGram φ c N y n) := by
  have hw : 0 < c / N := div_pos hc (by exact_mod_cast hN)
  set G := ∫ u, atomDilate φ (c / N) u ^ 2 with hG
  have hG0 : 0 < G := by rw [hG, integral_atomDilate_sq hw]; exact mul_pos hw hM
  have hnorm : ∀ s, bumpCorr (atomDilate φ (c / N)) s =
      G * (shellAutocorr φ (|s| / (c / N)) / (∫ t, φ t ^ 2)) := by
    intro s
    have := normalized_bumpCorr_atomDilate (φ := φ) hw s
    rw [← hG] at this
    field_simp at this ⊢
    linarith
  rw [← add_sum_erase _ _ hn]
  have hdiag : y n * bumpCorr (atomDilate φ (c / N)) (Real.log n - Real.log n) = G * y n := by
    rw [hnorm, sub_self, abs_zero, zero_div,
      show shellAutocorr φ 0 = ∫ t, φ t ^ 2 from shellAutocorr_zero (φ := φ), div_self hM.ne']
    ring
  rw [hdiag, mul_add]
  congr 1
  unfold nearGram
  rw [mul_sum, ← sum_filter_add_sum_filter_not ((Icc 1 N).erase n)
    (fun j : ℕ => |Real.log (j : ℝ) - Real.log n| ≤ 2 * c / N)]
  have hfar : (∑ j ∈ ((Icc 1 N).erase n).filter
      (fun j : ℕ => ¬(|Real.log (j : ℝ) - Real.log n| ≤ 2 * c / N)),
      y j * bumpCorr (atomDilate φ (c / N)) (Real.log n - Real.log j)) = 0 := by
    refine sum_eq_zero fun j hj => ?_
    have hfar := (mem_filter.mp hj).2
    rw [hnorm, shellAutocorr_eq_zero_of_one_le_abs hφ hsupp, zero_div, mul_zero, mul_zero]
    rw [abs_div, abs_of_pos hw, le_div_iff₀ hw, one_mul, abs_abs, abs_sub_comm]
    push Not at hfar
    have : 2 * c / N = 2 * (c / N) := by ring
    linarith
  rw [hfar, add_zero]
  have hset : ((Icc 1 N).erase n).filter (fun j : ℕ => |Real.log (j : ℝ) - Real.log n| ≤ 2 * c / N) =
      nearRowIndices c N n := by
    ext j; simp only [nearRowIndices, mem_filter, mem_erase]; tauto
  rw [hset]
  refine sum_congr rfl fun j _ => ?_
  rw [hnorm, abs_sub_comm]
  ring

/-- **The near Gram operator is controlled by its form.** With `λ = 1 + 2ec` the frame bound of
the atoms, `‖K₂ᵦ y‖² ≤ (λ − 2) ⟨Γ y, y⟩ + ‖y‖²`, `Γ = I + K₂ᵦ` the atomic Gram matrix. -/
theorem sum_nearGram_sq_le_gram {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ t, t ∉ Set.Icc 0 1 → φ t = 0) (hM : 0 < ∫ t, φ t ^ 2) {c : ℝ} {N : ℕ}
    (hc : 0 < c) (hcN : c ≤ N) (y : ℕ → ℝ) :
    (∑ n ∈ Icc 1 N, nearGram φ c N y n ^ 2) ≤
      (2 * Real.exp 1 * c - 1) *
          ((∑ n ∈ Icc 1 N, y n ^ 2) + ∑ n ∈ Icc 1 N, y n * nearGram φ c N y n) +
        ∑ n ∈ Icc 1 N, y n ^ 2 := by
  have hN : 0 < N := by exact_mod_cast hc.trans_le hcN
  have hw : 0 < c / N := div_pos hc (by exact_mod_cast hN)
  set g := atomDilate φ (c / N) with hg
  set G := ∫ u, g u ^ 2 with hG
  have hG0 : 0 < G := by rw [hG, hg, integral_atomDilate_sq hw]; exact mul_pos hw hM
  have hgcont : Continuous g := hφ.continuous.comp (continuous_id.div_const _)
  have hφc : HasCompactSupport φ := HasCompactSupport.intro isCompact_Icc fun u hu => hsupp u hu
  have hgc : HasCompactSupport g := hasCompactSupport_atomDilate hw.ne' hφc
  have hgsupp : ∀ u, u ∉ Set.Icc 0 (c / N) → g u = 0 := by
    intro u hu
    simp only [hg, atomDilate]
    apply hsupp
    rintro ⟨h0, h1⟩
    apply hu
    refine ⟨?_, (div_le_one hw).mp h1⟩
    by_contra hneg
    push Not at hneg
    have : u / (c / N) < 0 := div_neg_of_neg_of_pos hneg hw
    linarith
  have hnorm : ∀ s, bumpCorr g s = G * (shellAutocorr φ (|s| / (c / N)) / (∫ t, φ t ^ 2)) := by
    intro s
    have := normalized_bumpCorr_atomDilate (φ := φ) hw s
    rw [← hg, ← hG] at this
    field_simp at this ⊢
    linarith
  set bc : ℕ → ℕ → ℝ := fun m n => bumpCorr g (Real.log m - Real.log n) with hbc
  have hsym : ∀ m n, bc m n = bc n m := by
    intro m n; simp only [hbc, hnorm, abs_sub_comm]
  set z : ℕ → ℝ := fun n => y n + nearGram φ c N y n with hz
  have hrow : ∀ m ∈ Icc 1 N, (∑ n ∈ Icc 1 N, y n * bc m n) = G * z m := by
    intro m hm
    exact sum_bumpCorr_atomDilate_row hφ hsupp hM hc hN y hm
  have hrowz : ∀ m ∈ Icc 1 N, (∑ n ∈ Icc 1 N, bc m n * y n) = G * z m := by
    intro m hm; rw [← hrow m hm]; exact sum_congr rfl fun n _ => by ring
  set Z2 := ∑ m ∈ Icc 1 N, z m ^ 2 with hZ2
  set Q := ∑ m ∈ Icc 1 N, y m * z m with hQ
  have hZY : (∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, z m * y n * bc m n) = G * Z2 := by
    rw [hZ2, mul_sum]
    refine sum_congr rfl fun m hm => ?_
    rw [show (∑ n ∈ Icc 1 N, z m * y n * bc m n) = z m * ∑ n ∈ Icc 1 N, y n * bc m n by
      rw [mul_sum]; exact sum_congr rfl fun n _ => by ring, hrow m hm]
    ring
  have hYZ : (∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, y m * z n * bc m n) = G * Z2 := by
    rw [sum_comm, ← hZY]
    exact sum_congr rfl fun m _ => sum_congr rfl fun n _ => by rw [hsym]; ring
  have hYY : (∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, y m * y n * bc m n) = G * Q := by
    rw [hQ, mul_sum]
    refine sum_congr rfl fun m hm => ?_
    rw [show (∑ n ∈ Icc 1 N, y m * y n * bc m n) = y m * ∑ n ∈ Icc 1 N, y n * bc m n by
      rw [mul_sum]; exact sum_congr rfl fun n _ => by ring, hrow m hm]
    ring
  have hframe : (∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, z m * z n * bc m n) ≤
      G * (1 + 2 * Real.exp 1 * c) * Z2 := by
    have h1 := integral_atomicTest_mul_atomicTest hgcont hgc N N z z
    have h2 := integral_atomicTest_sq_le_of_le_horizon hgcont hgc hc hcN hgsupp z
    rw [← hG] at h2
    simp only [sq] at h2
    rw [← h1]
    simpa only [hZ2, sq] using h2
  set lamF := 1 + 2 * Real.exp 1 * c with hlamF
  have hlamF0 : 0 < lamF := by positivity
  set s := 1 / lamF with hs
  have hpos : 0 ≤ ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
      (s * z m - y m) * (s * z n - y n) * bc m n := by
    have h1 := integral_atomicTest_mul_atomicTest hgcont hgc N N
      (fun m => s * z m - y m) (fun m => s * z m - y m)
    rw [← h1]
    exact MeasureTheory.integral_nonneg fun u => mul_self_nonneg _
  have hexpand : (∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
      (s * z m - y m) * (s * z n - y n) * bc m n) =
      s ^ 2 * (∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, z m * z n * bc m n) -
        s * (∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, z m * y n * bc m n) -
        s * (∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, y m * z n * bc m n) +
        (∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, y m * y n * bc m n) := by
    simp only [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun m _ => sum_congr rfl fun n _ => ?_
    ring
  rw [hexpand, hZY, hYZ, hYY] at hpos
  have hZ20 : 0 ≤ Z2 := sum_nonneg fun _ _ => sq_nonneg _
  have hs0 : 0 < s := by positivity
  have hkey : Z2 ≤ lamF * Q := by
    have h3 : s ^ 2 * (∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, z m * z n * bc m n) ≤
        s ^ 2 * (G * lamF * Z2) := mul_le_mul_of_nonneg_left hframe (sq_nonneg _)
    have h4 : s ^ 2 * (G * lamF * Z2) = s * G * Z2 := by
      rw [hs]; field_simp
    have h5 : 0 ≤ s * G * Z2 - s * (G * Z2) - s * (G * Z2) + G * Q := by linarith
    have h6 : s * G * Z2 ≤ G * Q := by nlinarith
    have h7 : G * (s * Z2) ≤ G * Q := by linarith
    have h8 : s * Z2 ≤ Q := le_of_mul_le_mul_left h7 hG0
    rw [hs, one_div, inv_mul_le_iff₀ hlamF0] at h8
    exact h8
  have hnear : ∀ n, nearGram φ c N y n = z n - y n := fun n => by simp only [hz]; ring
  have hgoal : (∑ n ∈ Icc 1 N, nearGram φ c N y n ^ 2) = Z2 - 2 * Q + ∑ n ∈ Icc 1 N, y n ^ 2 := by
    simp only [hnear, hZ2, hQ]
    rw [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun n _ => ?_
    ring
  have hQeq : Q = (∑ n ∈ Icc 1 N, y n ^ 2) + ∑ n ∈ Icc 1 N, y n * nearGram φ c N y n := by
    rw [hQ, ← sum_add_distrib]
    refine sum_congr rfl fun n _ => ?_
    simp only [hz]; ring
  rw [hgoal]
  rw [← hQeq]
  have : lamF - 2 = 2 * Real.exp 1 * c - 1 := by rw [hlamF]; ring
  nlinarith

/-- **The near-Gram form of a packet without the pole conductor.** For `u = Σ_m a_m v_m` with
`a 1 = 0`: `|⟨K₂ᵦ u, u⟩| ≤ C (c⁵/N + (1 + log c) Sg/log N + c³R⁴/(N log N)) ‖u‖²`, where `Sg`
bounds `σ(m)/φ(m)` on the conductors. -/
theorem exists_nearGram_packet_form_le {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ t, t ∉ Set.Icc 0 1 → φ t = 0) (hM : 0 < ∫ t, φ t ^ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {R₂ N : ℕ} {c : ℝ}, 2 ≤ R₂ → R₂ * R₂ ≤ N →
      18 * (1 + Real.log R₂) ≤ Real.log N → 1 ≤ c → c / N ≤ 1 →
      4 * (linearNearRowRadius c + 1) ^ 2 ≤ N →
      ∀ {a : ℕ → ℝ}, a 1 = 0 → ∀ {Sg : ℝ},
        (∀ m ∈ Icc 2 R₂, (ArithmeticFunction.sigma 1 m : ℝ) / m.totient ≤ Sg) →
        |∑ n ∈ Icc 1 N,
          primeHorizonExtension (∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N) n *
            nearGram φ c N (primeHorizonExtension
              (∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N)) n| ≤
          C * (c ^ 5 / N + (1 + Real.log c) * Sg / Real.log N +
            c ^ 3 * (R₂ : ℝ) ^ 4 / (N * Real.log N)) *
            ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 := by
  obtain ⟨C_2, hC2, herr⟩ := exists_midBand_lag_sub_linearized_le hφ hsupp hM
  obtain ⟨C_4, hC4, hosc⟩ := exists_midBand_osc_sum_le hφ hsupp hM
  obtain ⟨C_m, hCm, hmean⟩ := exists_midBand_mean_sum_le_divisor_mean hφ hsupp
  refine ⟨2 / (∫ t, φ t ^ 2) * (C_2 + C_m + C_4), by positivity, ?_⟩
  intro R₂ N c hR₂ hR₂N hlog hc1 hw hradN a ha1 Sg hSg
  set u := ∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N with hu
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hL0 : 0 < Real.log N := by have := Real.log_natCast_nonneg R₂; linarith
  have hN0 : (0 : ℝ) < N := by
    have : (0 : ℝ) < 4 * (linearNearRowRadius c + 1) ^ 2 := by
      unfold linearNearRowRadius; positivity
    linarith
  have hHN : 2 * ⌊linearNearRowRadius c⌋₊ ≤ N := by
    have h0 : 0 ≤ linearNearRowRadius c := by unfold linearNearRowRadius; positivity
    have h1 : (⌊linearNearRowRadius c⌋₊ : ℝ) ≤ linearNearRowRadius c := Nat.floor_le h0
    have : ((2 * ⌊linearNearRowRadius c⌋₊ : ℕ) : ℝ) ≤ N := by
      push_cast; nlinarith
    exact_mod_cast this
  have hSg0 : 0 ≤ Sg := le_trans (by positivity) (hSg 2 (mem_Icc.mpr ⟨le_rfl, hR₂⟩))
  -- the form is the lead-kernel form over `∫φ²`
  have hform : (∑ n ∈ Icc 1 N, primeHorizonExtension u n * nearGram φ c N (primeHorizonExtension u) n) =
      (1 / ∫ t, φ t ^ 2) * ∑ n ∈ Icc 1 N, primeHorizonExtension u n *
        ∑ j ∈ nearRowIndices c N n, midBandLeadKernel φ c N n j * primeHorizonExtension u j := by
    rw [mul_sum]
    refine sum_congr rfl fun n _ => ?_
    unfold nearGram midBandLeadKernel
    rw [mul_sum, mul_sum, mul_sum]
    refine sum_congr rfl fun j _ => ?_
    rw [abs_sub_comm]
    ring
  have hlead := midBand_leadKernel_sum_eq (R₂ := R₂) hφ hsupp hL0 hc0 hw hradN a
  rw [← hu] at hlead
  rw [hform, hlead]
  have hlag : |midBandLagSum φ R₂ N c a| ≤
      (C_2 * (c ^ 5 * Real.log N / N) + C_m * (1 + Real.log c) * Sg +
        C_4 * (c ^ 3 * (R₂ : ℝ) ^ 4 / N)) * ‖u‖ ^ 2 := by
    have hid : midBandLagSum φ R₂ N c a =
        (midBandLagSum φ R₂ N c a - midBandLinearizedSum φ R₂ N c a) +
          midBandMeanSum φ R₂ N c a + midBandOscSum φ R₂ N c a := by
      linarith only [midBandLinearizedSum_eq_mean_add_osc φ R₂ N c a]
    have h1 := herr (R₂ := R₂) hL0 hc1 hradN a
    have h2 := hmean hR₂ hR₂N hlog hc1 hHN ha1 hSg
    have h3 := hosc hR₂ hR₂N hlog hc1 hradN a
    rw [← hu] at h1 h2 h3
    rw [hid]
    calc _ ≤ |midBandLagSum φ R₂ N c a - midBandLinearizedSum φ R₂ N c a| +
          |midBandMeanSum φ R₂ N c a| + |midBandOscSum φ R₂ N c a| := by
          have := abs_add_le (midBandLagSum φ R₂ N c a - midBandLinearizedSum φ R₂ N c a +
            midBandMeanSum φ R₂ N c a) (midBandOscSum φ R₂ N c a)
          have := abs_add_le (midBandLagSum φ R₂ N c a - midBandLinearizedSum φ R₂ N c a)
            (midBandMeanSum φ R₂ N c a)
          linarith
      _ ≤ _ := by nlinarith only [h1, h2, h3]
  have hu0 : 0 ≤ ‖u‖ ^ 2 := sq_nonneg _
  have hlc : 0 ≤ Real.log c := Real.log_nonneg hc1
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / ∫ t, φ t ^ 2), abs_mul, abs_mul,
    abs_of_pos (inv_pos.mpr hL0), abs_two]
  calc 1 / (∫ t, φ t ^ 2) * ((Real.log N)⁻¹ * (2 * |midBandLagSum φ R₂ N c a|))
      ≤ 1 / (∫ t, φ t ^ 2) * ((Real.log N)⁻¹ * (2 * ((C_2 * (c ^ 5 * Real.log N / N) +
          C_m * (1 + Real.log c) * Sg + C_4 * (c ^ 3 * (R₂ : ℝ) ^ 4 / N)) * ‖u‖ ^ 2))) := by
        gcongr
    _ = 2 / (∫ t, φ t ^ 2) * (C_2 * (c ^ 5 / N) + C_m * ((1 + Real.log c) * Sg / Real.log N) +
          C_4 * (c ^ 3 * (R₂ : ℝ) ^ 4 / (N * Real.log N))) * ‖u‖ ^ 2 := by
        field_simp
    _ ≤ 2 / (∫ t, φ t ^ 2) * ((C_2 + C_m + C_4) * (c ^ 5 / N + (1 + Real.log c) * Sg / Real.log N +
          c ^ 3 * (R₂ : ℝ) ^ 4 / (N * Real.log N))) * ‖u‖ ^ 2 := by
        gcongr
        have t1 : 0 ≤ c ^ 5 / N := by positivity
        have t2 : 0 ≤ (1 + Real.log c) * Sg / Real.log N := by positivity
        have t3 : 0 ≤ c ^ 3 * (R₂ : ℝ) ^ 4 / (N * Real.log N) := by positivity
        nlinarith
    _ = _ := by ring

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
