import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TerminalPaymentRetainsTheGrowingHighConductorGap
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.EveryCompactProfileHasAnExplicitTailClock

/-!
# Growing gaps on subpolynomial conductor cutoffs

The cutoff ratio tends to zero. A reciprocal square-root cap on the overlap
keeps its linear cost smaller than the logarithmic high-conductor gap.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Finset Filter Topology
open scoped Classical RealInnerProductSpace

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open CompletedArithmeticForms RenormalizedArithmeticPotentialTheory
  SpacingScaleHarmonicAnalysis

private theorem linear_high_rate_envelope {q L n c r Q ρ : ℝ}
    (hL1 : 1 ≤ L) (ht1 : 1 ≤ Real.log L) (hn1 : 1 ≤ n)
    (hc1 : 1 ≤ c) (hcT : c ≤ (Real.log L) ^ 2) (hcL : c ≤ L)
    (hr1 : 1 ≤ r) (hr : r ≤ n ^ (1 / 16 : ℝ))
    (hQ : L ^ q / 2 ≤ Q)
    (hfirst : c * (1 + Real.log r) / L ≤ Real.log L * Real.sqrt ρ) :
    c * (1 + Real.log r) / L + c ^ 2 * (1 + Real.log c) / L +
      c ^ 5 * L / n + c ^ 3 / Real.sqrt Q + c ^ 3 * r ^ 4 / n ≤
      Real.log L * Real.sqrt ρ + 2 * (Real.log L) ^ 5 / L +
        2 * ((Real.log L) ^ 6 / L ^ (q / 2)) +
        2 * (L ^ 6 / n ^ (1 / 4 : ℝ)) := by
  let t := Real.log L
  let V := L ^ 6 / n ^ (1 / 4 : ℝ)
  have hL : 0 < L := zero_lt_one.trans_le hL1
  have ht : 0 < t := zero_lt_one.trans_le ht1
  have hn : 0 < n := zero_lt_one.trans_le hn1
  have hc : 0 < c := zero_lt_one.trans_le hc1
  have hlogc0 : 0 ≤ 1 + Real.log c := by linarith only [Real.log_nonneg hc1]
  have hlogc : 1 + Real.log c ≤ 2 * t := by
    have hh := Real.log_le_log hc hcT
    rw [Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith only [hh, Real.log_le_sub_one_of_pos ht]
  have hsecond : c ^ 2 * (1 + Real.log c) / L ≤ 2 * t ^ 5 / L := by
    calc
      _ ≤ (t ^ 2) ^ 2 * (2 * t) / L := by gcongr
      _ = _ := by ring
  have hthird : c ^ 5 * L / n ≤ V := by
    calc
      _ ≤ L ^ 5 * L / n ^ (1 / 4 : ℝ) := by
        gcongr
        simpa only [Real.rpow_one] using
          Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num : (1 / 4 : ℝ) ≤ 1)
      _ = V := by dsimp only [V]; ring
  have hrpow : r ^ 4 ≤ n ^ (1 / 4 : ℝ) := by
    calc
      _ ≤ (n ^ (1 / 16 : ℝ)) ^ 4 := pow_le_pow_left₀ (zero_le_one.trans hr1) hr 4
      _ = _ := by rw [← Real.rpow_natCast, ← Real.rpow_mul hn.le]; norm_num
  have hfifth : c ^ 3 * r ^ 4 / n ≤ V := by
    calc
      _ ≤ L ^ 3 * n ^ (1 / 4 : ℝ) / n := by gcongr
      _ = L ^ 3 / n ^ (3 / 4 : ℝ) := by
        have hp : n ^ (1 / 4 : ℝ) * n ^ (3 / 4 : ℝ) = n := by
          rw [← Real.rpow_add hn]
          norm_num
        apply (div_eq_div_iff hn.ne' (Real.rpow_pos_of_pos hn (3 / 4 : ℝ)).ne').mpr
        rw [mul_assoc, hp]
      _ ≤ V := div_le_div₀ (pow_nonneg hL.le _)
        (pow_le_pow_right₀ hL1 (by norm_num)) (Real.rpow_pos_of_pos hn _)
        (Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num))
  have hQ0 : 0 < Q := (div_pos (Real.rpow_pos_of_pos hL q) zero_lt_two).trans_le hQ
  have hQroot : L ^ (q / 2) / 2 ≤ Real.sqrt Q := by
    have hsq : (L ^ (q / 2) / 2) ^ 2 ≤ Q := by
      rw [div_pow, ← Real.rpow_two, ← Real.rpow_mul hL.le,
        show q / 2 * 2 = q by ring]
      nlinarith only [hQ, Real.rpow_nonneg hL.le q]
    nlinarith only [hsq, Real.sq_sqrt hQ0.le, Real.sqrt_nonneg Q,
      Real.rpow_nonneg hL.le (q / 2)]
  have hfourth : c ^ 3 / Real.sqrt Q ≤ 2 * (t ^ 6 / L ^ (q / 2)) := by
    calc
      _ ≤ (t ^ 2) ^ 3 / (L ^ (q / 2) / 2) :=
        div_le_div₀ (pow_nonneg (sq_nonneg t) 3) (pow_le_pow_left₀ hc.le hcT 3)
          (div_pos (Real.rpow_pos_of_pos hL _) zero_lt_two) hQroot
      _ = _ := by ring
  dsimp only [V, t] at hsecond hthird hfourth hfifth
  linarith only [hfirst, hsecond, hthird, hfourth, hfifth]

private theorem terminal_coefficient_envelope {L n c r : ℝ}
    (hL1 : 1 ≤ L) (ht1 : 1 ≤ Real.log L) (hn1 : 1 ≤ n)
    (hc1 : 1 ≤ c) (hcT : c ≤ (Real.log L) ^ 2)
    (hr1 : 1 ≤ r) (hr : r ≤ n ^ (1 / 16 : ℝ))
    (hH : 1 + Real.log r ≤ L) :
    c ^ 4 * (1 + Real.log r) *
      ((1 + Real.log c) ^ 2 / L ^ 2 + r ^ 2 * (1 + Real.log c) / n) ≤
      4 * (Real.log L) ^ 10 / L + 2 * L ^ 10 / n ^ (7 / 8 : ℝ) := by
  let t := Real.log L
  have hL : 0 < L := zero_lt_one.trans_le hL1
  have ht : 0 < t := zero_lt_one.trans_le ht1
  have hn : 0 < n := zero_lt_one.trans_le hn1
  have hc : 0 < c := zero_lt_one.trans_le hc1
  have htL : t ≤ L := by dsimp only [t]; linarith only [Real.log_le_sub_one_of_pos hL]
  have hlogc0 : 0 ≤ 1 + Real.log c := by linarith only [Real.log_nonneg hc1]
  have hlogc : 1 + Real.log c ≤ 2 * t := by
    have hh := Real.log_le_log hc hcT
    rw [Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith only [hh, Real.log_le_sub_one_of_pos ht]
  have hH0 : 0 ≤ 1 + Real.log r := by linarith only [Real.log_nonneg hr1]
  have hrpow : r ^ 2 ≤ n ^ (1 / 8 : ℝ) := by
    calc
      _ ≤ (n ^ (1 / 16 : ℝ)) ^ 2 := pow_le_pow_left₀ (zero_le_one.trans hr1) hr 2
      _ = _ := by rw [← Real.rpow_natCast, ← Real.rpow_mul hn.le]; norm_num
  calc
    _ ≤ (t ^ 2) ^ 4 * L * ((2 * t) ^ 2 / L ^ 2 + n ^ (1 / 8 : ℝ) * (2 * t) / n) := by
      gcongr
    _ = 4 * t ^ 10 / L + 2 * (t ^ 9 * L) / n ^ (7 / 8 : ℝ) := by
      rw [show (7 / 8 : ℝ) = 1 - 1 / 8 by norm_num, Real.rpow_sub hn, Real.rpow_one]
      field_simp
      ring
    _ ≤ _ := by
      gcongr
      have hh := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ht.le htL 9) hL.le
      exact hh.trans_eq (by ring)

private theorem tendsto_log_power_div_nat_power (a : ℝ) {s : ℝ} (hs : 0 < s) :
    Tendsto (fun N : ℕ => Real.log (N : ℝ) ^ a / (N : ℝ) ^ s) atTop (𝓝 0) := by
  simpa only [Function.comp_def] using
    ((isLittleO_log_rpow_rpow_atTop a hs).tendsto_div_nhds_zero).comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop)

private theorem tendsto_loglog_power_div_log_power {e : ℝ} (he : 0 < e) (a : ℝ) :
    Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ)) ^ a / Real.log (N : ℝ) ^ e)
      atTop (𝓝 0) := by
  simpa only [Function.comp_def] using
    ((isLittleO_log_rpow_rpow_atTop a he).tendsto_div_nhds_zero).comp
      (Real.tendsto_log_atTop.comp
        (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop))

private theorem eventually_log_power_times_nat_power_le_nat (C a : ℝ) {p : ℝ}
    (hp : p < 1) :
    ∀ᶠ N : ℕ in atTop,
      C * Real.log (N : ℝ) ^ a * (N : ℝ) ^ p ≤ (N : ℝ) := by
  have hlim : Tendsto (fun N : ℕ =>
      C * (Real.log (N : ℝ) ^ a / (N : ℝ) ^ (1 - p))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero] using
      (((isLittleO_log_rpow_rpow_atTop a (sub_pos.mpr hp)).tendsto_div_nhds_zero).comp
        (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop)).const_mul C
  filter_upwards [hlim.eventually (ge_mem_nhds zero_lt_one), eventually_ge_atTop 1]
    with N hsmall hN1
  have hN : (0 : ℝ) < N := by exact_mod_cast hN1
  have hbound : C * Real.log (N : ℝ) ^ a ≤ (N : ℝ) ^ (1 - p) := by
    apply (div_le_one (Real.rpow_pos_of_pos hN (1 - p))).mp
    convert hsmall using 1; ring
  calc
    _ ≤ (N : ℝ) ^ (1 - p) * (N : ℝ) ^ p :=
      mul_le_mul_of_nonneg_right hbound (Real.rpow_nonneg hN.le p)
    _ = (N : ℝ) := by rw [← Real.rpow_add hN, sub_add_cancel, Real.rpow_one]


private theorem tendsto_linear_lag_envelope {q : ℝ} (hq : 0 < q) :
    Tendsto (fun N : ℕ =>
      2 * Real.log (Real.log (N : ℝ)) ^ 5 / Real.log N +
      2 * (Real.log (Real.log (N : ℝ)) ^ 6 / Real.log (N : ℝ) ^ (q / 2)) +
      2 * (Real.log (N : ℝ) ^ 6 / (N : ℝ) ^ (1 / 4 : ℝ))) atTop (𝓝 0) := by
  have h5 (x : ℝ) : x ^ (5 : ℝ) = x ^ (5 : ℕ) := Real.rpow_natCast x 5
  have h6 (x : ℝ) : x ^ (6 : ℝ) = x ^ (6 : ℕ) := Real.rpow_natCast x 6
  have h1 : Tendsto (fun N : ℕ =>
      Real.log (Real.log (N : ℝ)) ^ 5 / Real.log N) atTop (𝓝 0) := by
    simpa only [h5, Real.rpow_one] using tendsto_loglog_power_div_log_power zero_lt_one 5
  have h2 : Tendsto (fun N : ℕ =>
      Real.log (Real.log (N : ℝ)) ^ 6 / Real.log (N : ℝ) ^ (q / 2)) atTop (𝓝 0) := by
    simpa only [h6] using tendsto_loglog_power_div_log_power (div_pos hq zero_lt_two) 6
  have h3 : Tendsto (fun N : ℕ =>
      Real.log (N : ℝ) ^ 6 / (N : ℝ) ^ (1 / 4 : ℝ)) atTop (𝓝 0) := by
    simpa only [h6] using tendsto_log_power_div_nat_power 6 (by norm_num : (0 : ℝ) < 1 / 4)
  have hh := ((h1.const_mul 2).add (h2.const_mul 2)).add (h3.const_mul 2)
  simp only [mul_zero, add_zero] at hh
  apply hh.congr
  intro N
  ring

private theorem tendsto_terminal_envelope :
    Tendsto (fun N : ℕ => 4 * Real.log (Real.log (N : ℝ)) ^ 10 / Real.log N +
      2 * Real.log (N : ℝ) ^ 10 / (N : ℝ) ^ (7 / 8 : ℝ)) atTop (𝓝 0) := by
  have hp (x : ℝ) : x ^ (10 : ℝ) = x ^ (10 : ℕ) := Real.rpow_natCast x 10
  have h1 : Tendsto (fun N : ℕ =>
      Real.log (Real.log (N : ℝ)) ^ 10 / Real.log N) atTop (𝓝 0) := by
    simpa only [hp, Real.rpow_one] using tendsto_loglog_power_div_log_power zero_lt_one 10
  have h2 : Tendsto (fun N : ℕ =>
      Real.log (N : ℝ) ^ 10 / (N : ℝ) ^ (7 / 8 : ℝ)) atTop (𝓝 0) := by
    simpa only [hp] using tendsto_log_power_div_nat_power 10 (by norm_num : (0 : ℝ) < 7 / 8)
  have hh := (h1.const_mul 4).add (h2.const_mul 2)
  simp only [mul_zero, add_zero] at hh
  apply hh.congr
  intro N
  ring

/-- A cutoff containing the logarithmic block and having vanishing logarithmic
ratio satisfies every finite high-gap condition under the reciprocal-root clock. -/
theorem eventually_subpolynomial_high_band_horizon (R : ℕ → ℕ)
    (hRlow : ∀ N : ℕ, ⌊Real.log (N : ℝ)⌋₊ + 2 ≤ R N)
    (hρlim : Tendsto (fun N : ℕ => (1 + Real.log (R N)) / Real.log N) atTop (𝓝 0))
    {q C D : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) (hC : 0 < C) :
    ∀ᶠ N : ℕ in atTop,
      let Q := ⌊Real.log (N : ℝ) ^ q⌋₊
      2 ≤ Q ∧ Q ≤ R N ∧ (R N) ^ 6 ≤ N ∧
      1080 * (1 + Real.log (R N)) ≤ Real.log N ∧
      ∀ c : ℝ, 1 ≤ c → c ≤ Real.log (Real.log (N : ℝ)) ^ 2 →
        c ≤ Real.log (Real.log (N : ℝ)) /
          Real.sqrt ((1 + Real.log (R N)) / Real.log N) →
        c ≤ Real.log N ∧ c / N ≤ 1 / 3 ∧
        4 * (linearNearRowRadius c + 1) ^ 2 ≤ (N : ℝ) ∧
        ((R N * R N : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ N ∧
        4 * (Real.exp 1 + 3) ^ 2 * c ^ 2 ≤ (N : ℝ) ∧
        c ^ 4 * (1 + Real.log (R N)) *
          ((1 + Real.log c) ^ 2 / (Real.log N) ^ 2 +
            (R N : ℝ) ^ 2 * (1 + Real.log c) / N) ≤ 1 ∧
        Real.log c + D + C * (c * (1 + Real.log (R N)) / Real.log N +
          c ^ 2 * (1 + Real.log c) / Real.log N + c ^ 5 * Real.log N / N +
          c ^ 3 / Real.sqrt Q + c ^ 3 * (R N : ℝ) ^ 4 / N) + 1 ≤
          (1 / 4 : ℝ) * Real.log Q := by
  have hLlim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have htlim := Real.tendsto_log_atTop.comp hLlim
  have hQlim := (tendsto_rpow_atTop hq).comp hLlim
  have hwidthLim : Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ)) ^ 2 /
      Real.log N) atTop (𝓝 0) := by
    simpa only [Real.rpow_two, Real.rpow_one] using
      tendsto_loglog_power_div_log_power zero_lt_one 2
  have hgapLim : Tendsto (fun N : ℕ => Real.log (Real.log (Real.log (N : ℝ))) /
      Real.log (Real.log (N : ℝ))) atTop (𝓝 0) := by
    simpa only [Real.rpow_one, Function.comp_def] using
      ((isLittleO_log_rpow_rpow_atTop 1 zero_lt_one).tendsto_div_nhds_zero).comp htlim
  let Cnear := 2 * Real.exp 2 + 1
  have hCnear : 0 < Cnear := by dsimp only [Cnear]; positivity
  have hrootCap : 0 < q / (16 * C) := div_pos hq (by positivity)
  filter_upwards [eventually_ge_atTop 2, hLlim.eventually_ge_atTop 2,
    htlim.eventually_ge_atTop 1, hQlim.eventually_ge_atTop 2,
    hρlim.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 1080)),
    hρlim.eventually (ge_mem_nhds (sq_pos_of_pos hrootCap)),
    hwidthLim.eventually (ge_mem_nhds zero_lt_one),
    eventually_log_power_times_nat_power_le_nat 3 1 (by norm_num : (0 : ℝ) < 1),
    eventually_log_power_times_nat_power_le_nat (4 * Cnear ^ 2) 2 (by norm_num : (0 : ℝ) < 1),
    eventually_log_power_times_nat_power_le_nat (2 * Cnear) 1 (by norm_num : (1 / 8 : ℝ) < 1),
    eventually_log_power_times_nat_power_le_nat (4 * (Real.exp 1 + 3) ^ 2) 2
      (by norm_num : (0 : ℝ) < 1),
    (tendsto_linear_lag_envelope hq).eventually (ge_mem_nhds (one_div_pos.mpr hC)),
    tendsto_terminal_envelope.eventually (ge_mem_nhds zero_lt_one),
    htlim.eventually_ge_atTop (16 * (D + 2 + Real.log 2 / 4) / q),
    hgapLim.eventually (ge_mem_nhds (div_pos hq (by norm_num : (0 : ℝ) < 32)))]
    with N hN2 hL2 ht1 hQpow2 hρsmall hρroot hwidthSmall hwidthN hradN hsizeN
      hresWidthN hlagN hterminalN hgapN hgapSmall
  let L := Real.log (N : ℝ)
  let t := Real.log L
  let Q := ⌊L ^ q⌋₊
  let r := R N
  let ρ := (1 + Real.log r) / L
  have hL1 : 1 ≤ L := by linarith only [hL2]
  have hL : 0 < L := zero_lt_one.trans_le hL1
  have ht : 0 < t := zero_lt_one.trans_le ht1
  have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hr2 : 2 ≤ r := by have hh := hRlow N; dsimp only [r]; omega
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast (show 1 ≤ r by omega)
  have hr : (0 : ℝ) < r := zero_lt_one.trans_le hr1
  have hρ : 0 < ρ := div_pos (by positivity) hL
  have hroot : Real.sqrt ρ ≤ q / (16 * C) := by
    have hh := Real.sq_sqrt hρ.le
    change ρ ≤ (q / (16 * C)) ^ 2 at hρroot
    nlinarith only [hh, hρroot, Real.sqrt_nonneg ρ, hrootCap]
  have hframe : 1080 * (1 + Real.log r) ≤ L := by
    have hh := (div_le_iff₀ hL).mp hρsmall
    linarith only [hh]
  have hH : 1 + Real.log r ≤ L := by linarith only [hframe, Real.log_natCast_nonneg r]
  -- The small logarithmic ratio also supplies a fixed polynomial envelope.
  have hrpow : (r : ℝ) ≤ (N : ℝ) ^ (1 / 16 : ℝ) := by
    have hlogr : Real.log r ≤ L / 16 := by
      linarith only [hframe, Real.log_natCast_nonneg r]
    rw [Real.rpow_def_of_pos hN, ← Real.exp_log hr]
    exact Real.exp_le_exp.mpr (by change Real.log r ≤ L * (1 / 16 : ℝ); linarith only [hlogr])
  have hR6 : r ^ 6 ≤ N := by
    have hh : (r : ℝ) ^ 6 ≤ (N : ℝ) := by
      calc
        _ ≤ ((N : ℝ) ^ (1 / 16 : ℝ)) ^ 6 := pow_le_pow_left₀ (Nat.cast_nonneg _) hrpow 6
        _ = (N : ℝ) ^ (3 / 8 : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]
          norm_num
        _ ≤ (N : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
        _ = _ := Real.rpow_one _
    exact_mod_cast hh
  have hQ2 : 2 ≤ Q := Nat.le_floor hQpow2
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hQpow : (Q : ℝ) ≤ L ^ q := Nat.floor_le (Real.rpow_nonneg hL.le _)
  have hQR : Q ≤ r := by
    have hQL : L ^ q ≤ L := by simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hL1 hq1
    have hfloor := Nat.lt_floor_add_one L
    have hfloorR : ((⌊L⌋₊ + 2 : ℕ) : ℝ) ≤ r := by exact_mod_cast hRlow N
    have hh : (Q : ℝ) ≤ r := by push_cast at hfloorR; linarith only [hQpow, hQL, hfloor, hfloorR]
    exact_mod_cast hh
  have hQlower : L ^ q / 2 ≤ (Q : ℝ) := by
    have hh := Nat.lt_floor_add_one (L ^ q)
    change L ^ q < (Q : ℝ) + 1 at hh
    have hQcast : (2 : ℝ) ≤ Q := by exact_mod_cast hQ2
    linarith only [hh, hQcast]
  have hlogQ : q * t - Real.log 2 ≤ Real.log (Q : ℝ) := by
    have hh := Real.log_le_log (div_pos (Real.rpow_pos_of_pos hL _) zero_lt_two) hQlower
    rwa [Real.log_div (Real.rpow_pos_of_pos hL _).ne' (by norm_num), Real.log_rpow hL] at hh
  refine ⟨hQ2, hQR, hR6, hframe, ?_⟩
  intro c hc1 hcT hcCap
  have hc : 0 < c := zero_lt_one.trans_le hc1
  have hcL : c ≤ L := hcT.trans ((div_le_one hL).mp hwidthSmall)
  have hcN : c / N ≤ 1 / 3 := by
    apply (div_le_iff₀ hN).mpr
    have hh : 3 * L ≤ (N : ℝ) := by
      simpa only [Real.rpow_one, Real.rpow_zero, mul_one] using hwidthN
    linarith only [hcL, hh]
  have hrad : linearNearRowRadius c + 1 ≤ Cnear * L := by
    dsimp only [linearNearRowRadius, Cnear]
    have hh := mul_le_mul_of_nonneg_right hcL (Real.exp_pos 2).le
    nlinarith only [hh, hL1]
  have hrad0 : 0 ≤ linearNearRowRadius c + 1 := by
    dsimp only [linearNearRowRadius]
    positivity
  have hradSize : 4 * (linearNearRowRadius c + 1) ^ 2 ≤ (N : ℝ) := by
    calc
      _ ≤ 4 * (Cnear * L) ^ 2 := by gcongr
      _ = (4 * Cnear ^ 2) * L ^ (2 : ℝ) * (N : ℝ) ^ (0 : ℝ) := by
        rw [Real.rpow_two, Real.rpow_zero]; ring
      _ ≤ _ := hradN
  have hrTwo : (r : ℝ) ^ 2 ≤ (N : ℝ) ^ (1 / 8 : ℝ) := by
    calc
      _ ≤ ((N : ℝ) ^ (1 / 16 : ℝ)) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hrpow 2
      _ = _ := by rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]; norm_num
  have hRsum : ((r * r : ℕ) + 1 : ℝ) ≤ 2 * (N : ℝ) ^ (1 / 8 : ℝ) := by
    have hp := Real.one_le_rpow hN1 (by norm_num : (0 : ℝ) ≤ 1 / 8)
    push_cast
    nlinarith only [hrTwo, hp]
  have hsize : ((r * r : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ N := by
    calc
      _ ≤ (2 * (N : ℝ) ^ (1 / 8 : ℝ)) * (Cnear * L) := by gcongr
      _ = (2 * Cnear) * L ^ (1 : ℝ) * (N : ℝ) ^ (1 / 8 : ℝ) := by rw [Real.rpow_one]; ring
      _ ≤ _ := hsizeN
  have hraw : 4 * (Real.exp 1 + 3) ^ 2 * c ^ 2 ≤ (N : ℝ) :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hc.le hcL 2) (by positivity)).trans
      (by simpa only [Real.rpow_two, Real.rpow_zero, mul_one] using hresWidthN)
  have hterminal := (terminal_coefficient_envelope hL1 ht1 hN1 hc1 hcT hr1 hrpow hH).trans hterminalN
  -- The clock turns the linear cutoff cost into t * sqrt ρ = o(t).
  have hfirst : c * (1 + Real.log r) / L ≤ t * Real.sqrt ρ := by
    have hh := (le_div_iff₀ (Real.sqrt_pos.mpr hρ)).mp hcCap
    calc
      _ = (c * Real.sqrt ρ) * Real.sqrt ρ := by
        rw [mul_assoc, ← sq, Real.sq_sqrt hρ.le]
        dsimp only [ρ]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hh (Real.sqrt_nonneg ρ)
  have hrate := linear_high_rate_envelope hL1 ht1 hN1 hc1 hcT hcL hr1 hrpow hQlower hfirst
  have hcostRoot : C * (t * Real.sqrt ρ) ≤ q * t / 16 := by
    calc
      _ ≤ C * (t * (q / (16 * C))) := by gcongr
      _ = _ := by field_simp
  have hlogc : Real.log c ≤ 2 * Real.log t := by
    have hh := Real.log_le_log hc hcT
    simpa only [Real.log_pow, Nat.cast_ofNat] using hh
  have hlogSmall : Real.log c ≤ q * t / 16 := by
    have hh := (div_le_iff₀ ht).mp hgapSmall
    linarith only [hh, hlogc]
  have hconst : D + 2 + Real.log 2 / 4 ≤ q * t / 16 := by
    have hh := (div_le_iff₀ hq).mp hgapN
    change 16 * (D + 2 + Real.log 2 / 4) ≤ t * q at hh
    linarith only [hh]
  have hcancel : C * (1 / C) = 1 := by field_simp
  have hlagPaid := (mul_le_mul_of_nonneg_left hlagN hC.le).trans_eq hcancel
  have hratePaid := mul_le_mul_of_nonneg_left hrate hC.le
  have hgap : Real.log c + D + C * (c * (1 + Real.log r) / L +
      c ^ 2 * (1 + Real.log c) / L + c ^ 5 * L / N + c ^ 3 / Real.sqrt Q +
      c ^ 3 * (r : ℝ) ^ 4 / N) + 1 ≤ (1 / 4 : ℝ) * Real.log Q := by
    nlinarith only [hratePaid, hlagPaid, hcostRoot, hlogSmall, hconst, hlogQ, mul_nonneg hq.le ht.le]
  exact ⟨hcL, hcN, hradSize, hsize, hraw, hterminal, hgap⟩

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
