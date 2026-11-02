import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.EveryPolylogConductorSpanIsPositiveAtLogLogOverlap

/-!
# Almost-polynomial conductor spans retain high energy gaps

The high-conductor error vanishes on `R = floor(exp(log N/(log log N)^κ))`,
`κ > 2`, uniformly for `1 ≤ c ≤ (log log N) log log log N`. The small conductor cutoff
may be any fixed positive power of `log N`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Finset Filter Topology
open scoped Classical RealInnerProductSpace

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open CompletedArithmeticForms RenormalizedArithmeticPotentialTheory
  RenormalizedArithmeticPotentialTheory.CompletedShell SpacingScaleHarmonicAnalysis
  CriticalScaleArithmeticRigidity

/-- A conductor cutoff exceeding every fixed power of the logarithm. -/
def almostPolynomialConductorCutoff (κ : ℝ) (N : ℕ) : ℕ :=
  ⌊Real.exp (Real.log (N : ℝ) / Real.log (Real.log (N : ℝ)) ^ κ)⌋₊

private def highBandRate (c r q L n : ℝ) : ℝ :=
  c * (1 + Real.log c) * (1 + Real.log r) / L +
    c * (1 + Real.log r) / L + c ^ 2 / L +
    c ^ 2 * (1 + Real.log r) * (1 + Real.log c) / L +
    c ^ 2 * r * Real.sqrt (L / n) + c ^ 5 * L / n + c ^ 3 / Real.sqrt q +
    c ^ 3 * r ^ 4 / n + c ^ 2 * (1 + Real.log c) / L

private theorem high_band_rate_envelope {q κ L n c r Q : ℝ}
    (_hq : 0 < q) (hL1 : 1 ≤ L) (ht1 : 1 ≤ Real.log L) (hn1 : 1 ≤ n)
    (hc1 : 1 ≤ c) (hcT : c ≤ (Real.log L) ^ 2)
    (hcLog : c ≤ Real.log L * Real.log (Real.log L)) (hcL : c ≤ L)
    (hr1 : 1 ≤ r) (hr : r ≤ n ^ (1 / 16 : ℝ))
    (hlogr : Real.log r ≤ L / (Real.log L) ^ κ)
    (hQ : L ^ q / 2 ≤ Q) :
    highBandRate c r Q L n ≤
      10 * ((Real.log L) ^ 5 / L) +
      5 * ((Real.log (Real.log L)) ^ 2 * (1 + 2 * Real.log (Real.log L)) /
        (Real.log L) ^ (κ - 2)) +
      2 * ((Real.log L) ^ 6 / L ^ (q / 2)) +
      3 * (L ^ 6 / n ^ (1 / 4 : ℝ)) := by
  let t := Real.log L
  let M := 1 + 2 * Real.log t
  let U := t ^ 2 * (Real.log t) ^ 2 * M * (1 + L / t ^ κ) / L
  let V := L ^ 6 / n ^ (1 / 4 : ℝ)
  have hL : 0 < L := zero_lt_one.trans_le hL1
  have ht : 0 < t := zero_lt_one.trans_le ht1
  have hn : 0 < n := zero_lt_one.trans_le hn1
  have hc : 0 < c := zero_lt_one.trans_le hc1
  have hM : 1 ≤ M := by dsimp only [M]; linarith only [Real.log_nonneg ht1]
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hMt : M ≤ 2 * t := by
    dsimp only [M]
    linarith only [Real.log_le_sub_one_of_pos ht]
  have hlogc0 : 0 ≤ 1 + Real.log c := by linarith only [Real.log_nonneg hc1]
  have hlogc : 1 + Real.log c ≤ M := by
    have hh := Real.log_le_log hc hcT
    rw [Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    dsimp only [M]
    linarith only [hh]
  have hlogr0 : 0 ≤ 1 + Real.log r := by linarith only [Real.log_nonneg hr1]
  have hlogrUpper : 1 + Real.log r ≤ 1 + L / t ^ κ := by linarith only [hlogr]
  have huFac : 1 ≤ 1 + L / t ^ κ :=
    le_add_of_nonneg_right (div_nonneg hL.le (Real.rpow_nonneg ht.le κ))
  have hlogt0 : 0 ≤ Real.log t := Real.log_nonneg ht1
  have hcsq : c ^ 2 ≤ t ^ 2 * (Real.log t) ^ 2 := by
    simpa only [mul_pow] using pow_le_pow_left₀ hc.le hcLog 2
  have hcSq : c ≤ c ^ 2 := by nlinarith only [hc1]
  have h1 : c * (1 + Real.log c) * (1 + Real.log r) / L ≤ U := by
    dsimp only [U]
    gcongr
    exact hcSq.trans hcsq
  have h2 : c * (1 + Real.log r) / L ≤ U := by
    have hcm : c ≤ t ^ 2 * (Real.log t) ^ 2 * M :=
      (hcSq.trans hcsq).trans (le_mul_of_one_le_right (by positivity) hM)
    dsimp only [U]
    gcongr
  have h3 : c ^ 2 / L ≤ U := by
    have hh : c ^ 2 ≤ t ^ 2 * (Real.log t) ^ 2 * M * (1 + L / t ^ κ) :=
      (hcsq.trans (le_mul_of_one_le_right (by positivity) hM)).trans
        (le_mul_of_one_le_right (by positivity) huFac)
    exact div_le_div_of_nonneg_right hh hL.le
  have h4 : c ^ 2 * (1 + Real.log r) * (1 + Real.log c) / L ≤ U := by
    calc
      _ ≤ (t ^ 2 * (Real.log t) ^ 2) * (1 + L / t ^ κ) * M / L := by gcongr
      _ = U := by dsimp only [U]; ring
  have h9 : c ^ 2 * (1 + Real.log c) / L ≤ U := by
    calc
      _ ≤ (t ^ 2 * (Real.log t) ^ 2) * M / L := by gcongr
      _ ≤ U := by
        exact div_le_div_of_nonneg_right (le_mul_of_one_le_right (by positivity) huFac) hL.le
  have hsqrtn : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn
  have hsqrtRatio : Real.sqrt (L / n) ≤ L / Real.sqrt n := by
    apply (le_div_iff₀ hsqrtn).mpr
    have hsq : (Real.sqrt (L / n) * Real.sqrt n) ^ 2 = L := by
      rw [mul_pow, Real.sq_sqrt (div_nonneg hL.le hn.le), Real.sq_sqrt hn.le,
        div_mul_cancel₀ _ hn.ne']
    have hll : L ≤ L ^ 2 := by nlinarith only [hL1]
    nlinarith only [hsq, hll, hL.le,
      mul_nonneg (Real.sqrt_nonneg (L / n)) (Real.sqrt_nonneg n)]
  have hrquarter : r ≤ n ^ (1 / 4 : ℝ) := hr.trans
    (Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num))
  have h5 : c ^ 2 * r * Real.sqrt (L / n) ≤ V := by
    calc
      _ ≤ L ^ 2 * n ^ (1 / 4 : ℝ) * (L / Real.sqrt n) := by gcongr
      _ = L ^ 3 / n ^ (1 / 4 : ℝ) := by
        rw [Real.sqrt_eq_rpow,
          show (1 / 2 : ℝ) = 1 / 4 + 1 / 4 by norm_num, Real.rpow_add hn]
        field_simp
      _ ≤ V := div_le_div_of_nonneg_right
        (pow_le_pow_right₀ hL1 (by norm_num)) (Real.rpow_nonneg hn.le _)
  have h6 : c ^ 5 * L / n ≤ V := by
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
  have h8 : c ^ 3 * r ^ 4 / n ≤ V := by
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
  have h7 : c ^ 3 / Real.sqrt Q ≤ 2 * (t ^ 6 / L ^ (q / 2)) := by
    calc
      _ ≤ (t ^ 2) ^ 3 / (L ^ (q / 2) / 2) :=
        div_le_div₀ (pow_nonneg (sq_nonneg t) 3) (pow_le_pow_left₀ hc.le hcT 3)
          (div_pos (Real.rpow_pos_of_pos hL _) zero_lt_two) hQroot
      _ = _ := by ring
  have hU : U ≤ 2 * (t ^ 5 / L) + (Real.log t) ^ 2 * M / t ^ (κ - 2) := by
    have hlogt : Real.log t ≤ t := by linarith only [Real.log_le_sub_one_of_pos ht]
    calc
      _ = t ^ 2 * (Real.log t) ^ 2 * M / L + (Real.log t) ^ 2 * M / t ^ (κ - 2) := by
        dsimp only [U]
        rw [Real.rpow_sub ht, Real.rpow_two]
        field_simp
      _ ≤ _ := by
        have hh : t ^ 2 * (Real.log t) ^ 2 * M ≤ t ^ 2 * t ^ 2 * (2 * t) := by gcongr
        exact add_le_add ((div_le_div_of_nonneg_right hh hL.le).trans_eq (by ring)) le_rfl
  dsimp only [highBandRate]
  calc
    _ ≤ 5 * U + 2 * (t ^ 6 / L ^ (q / 2)) + 3 * V := by
      linarith only [h1, h2, h3, h4, h5, h6, h7, h8, h9]
    _ ≤ _ := by
      dsimp only [V, M, t] at *
      linarith only [hU]

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

private theorem tendsto_high_band_envelope {q κ : ℝ} (hq : 0 < q) (hκ : 2 < κ) :
    Tendsto (fun N : ℕ =>
      10 * (Real.log (Real.log (N : ℝ)) ^ 5 / Real.log N) +
      5 * (Real.log (Real.log (Real.log (N : ℝ))) ^ 2 *
        (1 + 2 * Real.log (Real.log (Real.log (N : ℝ)))) /
        Real.log (Real.log (N : ℝ)) ^ (κ - 2)) +
      2 * (Real.log (Real.log (N : ℝ)) ^ 6 / Real.log (N : ℝ) ^ (q / 2)) +
      3 * (Real.log (N : ℝ) ^ 6 / (N : ℝ) ^ (1 / 4 : ℝ))) atTop (𝓝 0) := by
  have hLlim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have htlim := Real.tendsto_log_atTop.comp hLlim
  have h₁ : Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ)) ^ 5 / Real.log N)
      atTop (𝓝 0) := by
    have hp (x : ℝ) : x ^ (5 : ℝ) = x ^ (5 : ℕ) := Real.rpow_natCast x 5
    simpa only [hp, Real.rpow_one] using tendsto_loglog_power_div_log_power zero_lt_one 5
  have hκ0 : 0 < κ - 2 := sub_pos.mpr hκ
  have hlogpow (j : ℕ) : Tendsto (fun N : ℕ =>
      Real.log (Real.log (Real.log (N : ℝ))) ^ j /
        Real.log (Real.log (N : ℝ)) ^ (κ - 2)) atTop (𝓝 0) := by
    have hp (x : ℝ) : x ^ (j : ℝ) = x ^ j := Real.rpow_natCast x j
    simpa only [Function.comp_def, hp] using
      ((isLittleO_log_rpow_rpow_atTop (j : ℝ) hκ0).tendsto_div_nhds_zero).comp htlim
  have h₂ : Tendsto (fun N : ℕ =>
      Real.log (Real.log (Real.log (N : ℝ))) ^ 2 *
        (1 + 2 * Real.log (Real.log (Real.log (N : ℝ)))) /
        Real.log (Real.log (N : ℝ)) ^ (κ - 2)) atTop (𝓝 0) := by
    have hh := (hlogpow 2).add ((hlogpow 3).const_mul 2)
    simp only [mul_zero, add_zero] at hh
    apply hh.congr
    intro N
    ring
  have h₃ : Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ)) ^ 6 /
      Real.log (N : ℝ) ^ (q / 2)) atTop (𝓝 0) := by
    have hp (x : ℝ) : x ^ (6 : ℝ) = x ^ (6 : ℕ) := Real.rpow_natCast x 6
    simpa only [hp] using tendsto_loglog_power_div_log_power (div_pos hq zero_lt_two) 6
  have h₄ : Tendsto (fun N : ℕ => Real.log (N : ℝ) ^ 6 / (N : ℝ) ^ (1 / 4 : ℝ))
      atTop (𝓝 0) := by
    have hp (x : ℝ) : x ^ (6 : ℝ) = x ^ (6 : ℕ) := Real.rpow_natCast x 6
    simpa only [hp] using tendsto_log_power_div_nat_power 6 (by norm_num : (0 : ℝ) < 1 / 4)
  simpa only [mul_zero, add_zero] using
    (((h₁.const_mul 10).add (h₂.const_mul 5)).add (h₃.const_mul 2)).add (h₄.const_mul 3)

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


/-- All geometric and error conditions for the logarithmic high-conductor gap hold
on the almost-polynomial cutoff beyond each fixed log-log multiple. -/
theorem eventually_almost_polynomial_high_band_horizon {q κ C H : ℝ}
    (hq : 0 < q) (hκ : 2 < κ) (hC : 0 < C) :
    ∀ᶠ N : ℕ in atTop,
      let Q := ⌊Real.log (N : ℝ) ^ q⌋₊
      let R := almostPolynomialConductorCutoff κ N
      2 ≤ Q ∧ Q ≤ R ∧ R ^ 6 ≤ N ∧ 36 * (1 + Real.log R) ≤ Real.log N ∧
      ∀ c : ℝ, 1 ≤ c → c ≤ Real.log (Real.log (N : ℝ)) ^ 2 →
        c ≤ Real.log (Real.log (N : ℝ)) * Real.log (Real.log (Real.log (N : ℝ))) →
        c ≤ Real.log N ∧ c / N ≤ 1 / 3 ∧
        4 * (linearNearRowRadius c + 1) ^ 2 ≤ (N : ℝ) ∧
        ((R * R : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ N ∧
        4 * (Real.exp 1 + 3) ^ 2 * c ^ 2 ≤ (N : ℝ) ∧
        C * (c * (1 + Real.log c) * (1 + Real.log R) / Real.log N +
          c * (1 + Real.log R) / Real.log N + c ^ 2 / Real.log N +
          c ^ 2 * (1 + Real.log R) * (1 + Real.log c) / Real.log N +
          c ^ 2 * (R : ℝ) * Real.sqrt (Real.log N / N) +
          c ^ 5 * Real.log N / N + c ^ 3 / Real.sqrt Q +
          c ^ 3 * (R : ℝ) ^ 4 / N + c ^ 2 * (1 + Real.log c) / Real.log N) ≤ 1 ∧
        H + 1 + Real.log c ≤ (1 / 4 : ℝ) * Real.log Q := by
  have hLlim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have htlim := Real.tendsto_log_atTop.comp hLlim
  have hQlim := (tendsto_rpow_atTop hq).comp hLlim
  have hκpos : 0 < κ := by linarith only [hκ]
  have hκlim := (tendsto_rpow_atTop hκpos).comp htlim
  have hqrLim := (tendsto_loglog_power_div_log_power zero_lt_one (κ + 1)).const_mul q
  simp only [Real.rpow_one, mul_zero] at hqrLim
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
  have hsmall := (tendsto_high_band_envelope hq hκ).eventually
    (ge_mem_nhds (one_div_pos.mpr hC))
  filter_upwards [eventually_ge_atTop 2, hLlim.eventually_ge_atTop 72,
    htlim.eventually_ge_atTop 1, hQlim.eventually_ge_atTop 2,
    hκlim.eventually_ge_atTop 72,
    hqrLim.eventually (ge_mem_nhds zero_lt_one),
    hwidthLim.eventually (ge_mem_nhds zero_lt_one),
    eventually_log_power_times_nat_power_le_nat 3 1 (by norm_num : (0 : ℝ) < 1),
    eventually_log_power_times_nat_power_le_nat (4 * Cnear ^ 2) 2 (by norm_num : (0 : ℝ) < 1),
    eventually_log_power_times_nat_power_le_nat (2 * Cnear) 1 (by norm_num : (1 / 8 : ℝ) < 1),
    eventually_log_power_times_nat_power_le_nat (4 * (Real.exp 1 + 3) ^ 2) 2
      (by norm_num : (0 : ℝ) < 1), hsmall,
    htlim.eventually_ge_atTop (8 * (H + 1 + Real.log 2 / 4) / q),
    hgapLim.eventually (ge_mem_nhds (div_pos hq (by norm_num : (0 : ℝ) < 32)))]
    with N hN2 hL72 ht1 hQpow2 hκ72 hqrSmall hwidthSmall hwidthN hradN hsizeN
      hreswidthN hsmallN hgapN hgapSmall
  let L := Real.log (N : ℝ)
  let t := Real.log L
  let Q := ⌊L ^ q⌋₊
  let R := almostPolynomialConductorCutoff κ N
  change 1 ≤ t at ht1
  change 72 ≤ t ^ κ at hκ72
  have hL1 : 1 ≤ L := by linarith only [hL72]
  have hL : 0 < L := zero_lt_one.trans_le hL1
  have ht : 0 < t := zero_lt_one.trans_le ht1
  have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hQ2 : 2 ≤ Q := Nat.le_floor hQpow2
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hQpow : (Q : ℝ) ≤ L ^ q := Nat.floor_le (Real.rpow_nonneg hL.le _)
  have hRexp : (R : ℝ) ≤ Real.exp (L / t ^ κ) := Nat.floor_le (Real.exp_pos _).le
  have hqexp : L ^ q ≤ Real.exp (L / t ^ κ) := by
    rw [Real.rpow_def_of_pos hL]
    apply Real.exp_le_exp.mpr
    apply (le_div_iff₀ (Real.rpow_pos_of_pos ht κ)).mpr
    have hh : q * t ^ (κ + 1) ≤ L := by
      apply (div_le_one hL).mp
      convert hqrSmall using 1; ring
    rw [Real.rpow_add ht, Real.rpow_one] at hh
    change t * q * t ^ κ ≤ L
    nlinarith only [hh]
  have hQR : Q ≤ R := Nat.le_floor (hQpow.trans hqexp)
  have hR1 : (1 : ℝ) ≤ R := by exact_mod_cast (show 1 ≤ R by omega)
  have hlogR : Real.log (R : ℝ) ≤ L / t ^ κ := by
    have hh := Real.log_le_log (zero_lt_one.trans_le hR1) hRexp
    rwa [Real.log_exp] at hh
  have hRpow : (R : ℝ) ≤ (N : ℝ) ^ (1 / 16 : ℝ) := by
    apply hRexp.trans
    rw [Real.rpow_def_of_pos hN]
    apply Real.exp_le_exp.mpr
    have hh : L / t ^ κ ≤ L / 16 := div_le_div_of_nonneg_left hL.le
      (by norm_num) (by linarith only [hκ72])
    simpa only [div_eq_mul_inv, one_mul] using hh
  have hR6 : R ^ 6 ≤ N := by
    have hh : (R : ℝ) ^ 6 ≤ (N : ℝ) := by
      calc
        _ ≤ ((N : ℝ) ^ (1 / 16 : ℝ)) ^ 6 := pow_le_pow_left₀ (Nat.cast_nonneg _) hRpow 6
        _ = (N : ℝ) ^ (3 / 8 : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]
          norm_num
        _ ≤ (N : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
        _ = _ := Real.rpow_one _
    exact_mod_cast hh
  have hgram : 36 * (1 + Real.log R) ≤ L := by
    have hh : L / t ^ κ ≤ L / 72 := div_le_div_of_nonneg_left hL.le (by norm_num) hκ72
    linarith only [hlogR, hh, hL72]
  have hQlower : L ^ q / 2 ≤ (Q : ℝ) := by
    have hh := Nat.lt_floor_add_one (L ^ q)
    change L ^ q < (Q : ℝ) + 1 at hh
    have hQcast : (2 : ℝ) ≤ Q := by exact_mod_cast hQ2
    linarith only [hh, hQcast]
  have hlogQ : q * t - Real.log 2 ≤ Real.log (Q : ℝ) := by
    have hh := Real.log_le_log (div_pos (Real.rpow_pos_of_pos hL _) zero_lt_two) hQlower
    rwa [Real.log_div (Real.rpow_pos_of_pos hL _).ne' (by norm_num), Real.log_rpow hL] at hh
  refine ⟨hQ2, hQR, hR6, hgram, ?_⟩
  intro c hc1 hcT hcLog
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
  have hrad0 : 0 ≤ linearNearRowRadius c + 1 := by unfold linearNearRowRadius; positivity
  have hradBound : 4 * (linearNearRowRadius c + 1) ^ 2 ≤ (N : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hrad0 hrad 2) (by norm_num : (0 : ℝ) ≤ 4)
    have hNrad : 4 * Cnear ^ 2 * L ^ 2 ≤ (N : ℝ) := by
      simpa only [Real.rpow_two, Real.rpow_zero, mul_one] using hradN
    nlinarith only [hh, hNrad]
  have hRtwo : (R : ℝ) ^ 2 ≤ (N : ℝ) ^ (1 / 8 : ℝ) := by
    calc
      _ ≤ ((N : ℝ) ^ (1 / 16 : ℝ)) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hRpow 2
      _ = _ := by rw [← Real.rpow_two, ← Real.rpow_mul hN.le]; norm_num
  have hRsum : ((R * R : ℕ) + 1 : ℝ) ≤ 2 * (N : ℝ) ^ (1 / 8 : ℝ) := by
    have hp : 1 ≤ (N : ℝ) ^ (1 / 8 : ℝ) := Real.one_le_rpow hN1 (by norm_num)
    push_cast
    nlinarith only [hRtwo, hp]
  have hsize : ((R * R : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ N := by
    calc
      _ ≤ (2 * (N : ℝ) ^ (1 / 8 : ℝ)) * (Cnear * L) :=
        mul_le_mul hRsum hrad hrad0 (by positivity)
      _ = (2 * Cnear) * L ^ (1 : ℝ) * (N : ℝ) ^ (1 / 8 : ℝ) := by
        rw [Real.rpow_one]; ring
      _ ≤ _ := hsizeN
  have hresWidth : 4 * (Real.exp 1 + 3) ^ 2 * c ^ 2 ≤ (N : ℝ) := by
    exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hc.le hcL 2) (by positivity)).trans
      (by simpa only [Real.rpow_two, Real.rpow_zero, mul_one] using hreswidthN)
  have hsmallRate : C * highBandRate c R Q L N ≤ 1 := by
    have hh := (high_band_rate_envelope hq hL1 ht1 hN1 hc1 hcT hcLog hcL hR1 hRpow
      hlogR hQlower).trans hsmallN
    have hm := mul_le_mul_of_nonneg_left hh hC.le
    simpa only [mul_one_div_cancel hC.ne'] using hm
  have hgap : H + 1 + Real.log c ≤ (1 / 4 : ℝ) * Real.log Q := by
    have hlogc : Real.log c ≤ 2 * Real.log t := by
      have hh := Real.log_le_log hc hcT
      simpa only [Real.log_pow, Nat.cast_ofNat] using hh
    have hlogt : Real.log t ≤ q * t / 32 := by
      have hh := (div_le_iff₀ ht).mp hgapSmall
      change Real.log t ≤ (q / 32) * t at hh
      linarith only [hh]
    have hconst := (div_le_iff₀ hq).mp hgapN
    change 8 * (H + 1 + Real.log 2 / 4) ≤ t * q at hconst
    have hqt : 0 ≤ q * t := mul_nonneg hq.le ht.le
    nlinarith only [hlogc, hlogt, hlogQ, hconst, hqt]
  exact ⟨hcL, hcN, hradBound, hsize, hresWidth, hsmallRate, hgap⟩

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
