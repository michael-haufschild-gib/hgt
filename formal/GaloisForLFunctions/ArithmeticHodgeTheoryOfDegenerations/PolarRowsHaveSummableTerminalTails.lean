import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TerminalWindowsReadThePolarCenter
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheLogarithmicWeightOfTheNearPairs
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TopWindowConductorRowCancellation

/-!
# Summable terminal tails of the polar rows

The exact harmonic center has a logarithmic endpoint singularity. Its last
`K ≤ N/2` rows have normalized square mass bounded by `50 K/N + 64 √(K/N)`.
The overlap logarithm times the polar Gram-row defect also vanishes in square norm.
-/

set_option autoImplicit false
noncomputable section
open Finset Filter Topology
open scoped BigOperators
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open CriticalArithmeticCorrelationTheory RenormalizedArithmeticPotentialTheory
  RenormalizedArithmeticPotentialTheory.CompletedShell SpacingScaleHarmonicAnalysis

/-- A quarter-power bound makes the squared terminal logarithm summable. -/
lemma log_sq_le_sixteen_sqrt {x : ℝ} (hx : 1 ≤ x) :
    Real.log x ^ 2 ≤ 16 * Real.sqrt x := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hlog := Real.log_le_rpow_div hx0.le (by norm_num : (0 : ℝ) < 1 / 4)
  have hs := pow_le_pow_left₀ (Real.log_nonneg hx) hlog 2
  have hp : (x ^ (1 / 4 : ℝ)) ^ 2 = Real.sqrt x := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    norm_num only [Nat.cast_ofNat, show (1 / 4 : ℝ) * 2 = 1 / 2 by norm_num]
    exact (Real.sqrt_eq_rpow x).symm
  norm_num [div_pow, hp] at hs
  nlinarith only [hs]

/-- A discrete squared logarithm has a uniformly small terminal tail. -/
lemma sum_log_ratio_sq_le {K N : ℕ} (hKN : K ≤ N) :
    (∑ k ∈ Ioc 0 K, Real.log ((N : ℝ) / k) ^ 2) ≤
      32 * Real.sqrt N * Real.sqrt K := by
  have hsum : (∑ k ∈ Ioc 0 K, 1 / Real.sqrt k) ≤ 2 * Real.sqrt K := by
    have he : Ioc 0 K = Icc 1 K := by
      ext k
      simp only [mem_Ioc, mem_Icc]
      omega
    rw [he, ← sum_range_succ_eq_sum_Icc]
    simpa only [Nat.cast_add, Nat.cast_one] using sum_inv_sqrt_succ_le K
  have hpoint : ∀ k ∈ Ioc 0 K, Real.log ((N : ℝ) / k) ^ 2 ≤
      (16 * Real.sqrt N) * (1 / Real.sqrt k) := by
    intro k hk
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (mem_Ioc.mp hk).1
    have hratio : 1 ≤ (N : ℝ) / k := (le_div_iff₀ hk0).mpr (by
      simpa only [one_mul] using (show (k : ℝ) ≤ N by exact_mod_cast (mem_Ioc.mp hk).2.trans hKN))
    have hh := log_sq_le_sixteen_sqrt hratio
    rw [Real.sqrt_div (Nat.cast_nonneg N)] at hh
    exact hh.trans_eq (by ring)
  calc
    _ ≤ ∑ k ∈ Ioc 0 K, (16 * Real.sqrt N) * (1 / Real.sqrt k) := sum_le_sum hpoint
    _ = (16 * Real.sqrt N) * ∑ k ∈ Ioc 0 K, (1 / Real.sqrt k) := (mul_sum _ _ _).symm
    _ ≤ (16 * Real.sqrt N) * (2 * Real.sqrt K) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

/-- The squared logarithmic tail is uniformly integrable in the discrete horizon. -/
lemma normalized_sum_log_ratio_sq_le {N : ℕ} (hN : 1 ≤ N)
    {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    (∑ k ∈ Ioc 0 ⌊η * (N : ℝ)⌋₊, Real.log ((N : ℝ) / k) ^ 2) / N ≤
      32 * Real.sqrt η := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hKN : ⌊η * (N : ℝ)⌋₊ ≤ N := by
    exact (Nat.floor_mono (mul_le_mul_of_nonneg_right hη1 hN0.le)).trans_eq
      (by rw [one_mul, Nat.floor_natCast])
  have hK := Real.sqrt_le_sqrt (Nat.floor_le (mul_nonneg hη0 hN0.le))
  rw [Real.sqrt_mul hη0] at hK
  calc
    _ ≤ (32 * Real.sqrt N * Real.sqrt ⌊η * (N : ℝ)⌋₊) / N :=
      div_le_div_of_nonneg_right (sum_log_ratio_sq_le hKN) hN0.le
    _ ≤ (32 * Real.sqrt N * (Real.sqrt η * Real.sqrt N)) / N :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hK (by positivity)) hN0.le
    _ = (32 * Real.sqrt η) * ((Real.sqrt N * Real.sqrt N) / N) := by ring
    _ = _ := by rw [Real.mul_self_sqrt hN0.le, div_self hN0.ne', mul_one]

/-- The exact polar center has only a logarithmic terminal singularity, including its last row. -/
lemma abs_polarCenterRow_le {N n : ℕ} (hn : n ∈ Icc 1 N) :
    |polarCenterRow N n| ≤ (N : ℝ) / n + 3 +
      Real.log ((N : ℝ) / (N - n + 1 : ℕ)) := by
  have hn1 := (mem_Icc.mp hn).1
  have hnN := (mem_Icc.mp hn).2
  have hN1 : 1 ≤ N := hn1.trans hnN
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hk0 : (0 : ℝ) < (N - n + 1 : ℕ) := by positivity
  have hkN : (N - n + 1 : ℕ) ≤ N := by omega
  have hratio : 0 ≤ Real.log ((N : ℝ) / (N - n + 1 : ℕ)) :=
    Real.log_nonneg ((le_div_iff₀ hk0).mpr (by
      simpa only [one_mul] using (show ((N - n + 1 : ℕ) : ℝ) ≤ N by exact_mod_cast hkN)))
  have hlogratio : Real.log ((N : ℝ) / (N - n + 1 : ℕ)) =
      Real.log N - Real.log (N - n + 1 : ℕ) := Real.log_div hN0.ne' hk0.ne'
  have hHNhi := harmonic_le_one_add_log N
  have hHNlo : Real.log (N : ℝ) ≤ (harmonic N : ℝ) :=
    (Real.log_le_log hN0 (by exact_mod_cast Nat.le_succ N)).trans (log_add_one_le_harmonic N)
  have hHklo := log_add_one_le_harmonic (N - n)
  have hHkhi : (harmonic (N - n) : ℝ) ≤ 1 + Real.log N := by
    by_cases hk : N - n = 0
    · rw [hk, harmonic_zero, Rat.cast_zero]
      have := Real.log_nonneg (show (1 : ℝ) ≤ N by exact_mod_cast hN1)
      linarith only [this]
    · exact (harmonic_le_one_add_log (N - n)).trans (add_le_add le_rfl
        (Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hk)
          (by exact_mod_cast Nat.sub_le N n)))
  have hHpluslo : Real.log (N : ℝ) ≤ (harmonic (N + n) : ℝ) :=
    (Real.log_le_log hN0 (by exact_mod_cast (show N ≤ N + n + 1 by omega))).trans
      (log_add_one_le_harmonic (N + n))
  have hHplushi : (harmonic (N + n) : ℝ) ≤ 2 + Real.log N := by
    have hnp0 : (0 : ℝ) < (N + n : ℕ) := by positivity
    have hh := Real.log_le_log hnp0
      (show ((N + n : ℕ) : ℝ) ≤ 2 * N by exact_mod_cast (by omega : N + n ≤ 2 * N))
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hN0.ne'] at hh
    have hl2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    have hup := harmonic_le_one_add_log (N + n)
    linarith only [hh, hl2, hup]
  have hfrac : 0 ≤ (N : ℝ) / n := by positivity
  have hsmall : 0 ≤ 3 / (4 * (n : ℝ)) := by positivity
  have hsmall1 : 3 / (4 * (n : ℝ)) ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    linarith only [this]
  rw [abs_le]
  dsimp only [polarCenterRow]
  constructor <;> linarith only [hHNhi, hHNlo, hHklo, hHkhi, hHpluslo,
    hHplushi, hfrac, hsmall, hsmall1, hratio, hlogratio]

/-- Reversing the final rows turns their logarithmic singularity into a summable initial segment. -/
lemma sum_terminal_log_ratio_sq_eq {K N : ℕ} (hKN : K ≤ N) :
    (∑ n ∈ Ioc (N - K) N, Real.log ((N : ℝ) / (N - n + 1 : ℕ)) ^ 2) =
      ∑ k ∈ Ioc 0 K, Real.log ((N : ℝ) / k) ^ 2 := by
  refine sum_bij (fun n _ => N - n + 1) ?_ ?_ ?_ ?_
  · intro n hn
    simp only [mem_Ioc] at hn ⊢
    omega
  · intro n hn m hm he
    simp only [mem_Ioc] at hn hm
    omega
  · intro k hk
    simp only [mem_Ioc] at hk
    refine ⟨N - k + 1, ?_, ?_⟩
    · simp only [mem_Ioc]; omega
    · omega
  · intro n hn
    rfl

/-- The last `K ≤ N/2` polar-center rows have uniformly vanishing normalized square mass. -/
lemma normalized_sum_terminal_polarCenterRow_sq_le {K N : ℕ}
    (hN : 1 ≤ N) (hK : 2 * K ≤ N) :
    (∑ n ∈ Ioc (N - K) N, polarCenterRow N n ^ 2) / N ≤
      50 * ((K : ℝ) / N) + 64 * Real.sqrt ((K : ℝ) / N) := by
  have hKN : K ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hpt : ∀ n ∈ Ioc (N - K) N, polarCenterRow N n ^ 2 ≤
      50 + 2 * Real.log ((N : ℝ) / (N - n + 1 : ℕ)) ^ 2 := by
    intro n hn
    have hnN := (mem_Ioc.mp hn).2
    have hn1 : 1 ≤ n := by have := (mem_Ioc.mp hn).1; omega
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have htwo : N ≤ 2 * n := by have := (mem_Ioc.mp hn).1; omega
    have hratio : (N : ℝ) / n ≤ 2 := (div_le_iff₀ hn0).mpr (by exact_mod_cast htwo)
    have hb := abs_polarCenterRow_le (mem_Icc.mpr ⟨hn1, hnN⟩)
    have hlog0 : 0 ≤ Real.log ((N : ℝ) / (N - n + 1 : ℕ)) :=
      Real.log_nonneg ((le_div_iff₀ (by positivity)).mpr (by
        simp only [one_mul]
        exact_mod_cast (show N - n + 1 ≤ N by omega)))
    have hab : |polarCenterRow N n| ≤ 5 + Real.log ((N : ℝ) / (N - n + 1 : ℕ)) := by
      linarith only [hb, hratio]
    have hs := pow_le_pow_left₀ (abs_nonneg _) hab 2
    rw [sq_abs] at hs
    nlinarith only [hs, sq_nonneg (5 - Real.log ((N : ℝ) / (N - n + 1 : ℕ)))]
  have hsum := sum_le_sum hpt
  rw [sum_add_distrib, sum_const, ← mul_sum, Nat.card_Ioc, Nat.sub_sub_self hKN,
    nsmul_eq_mul, sum_terminal_log_ratio_sq_eq hKN] at hsum
  have hlog := sum_log_ratio_sq_le hKN
  have htotal : (∑ n ∈ Ioc (N - K) N, polarCenterRow N n ^ 2) ≤
      50 * K + 64 * Real.sqrt N * Real.sqrt K := by
    linarith only [hsum, hlog]
  calc
    _ ≤ (50 * K + 64 * Real.sqrt N * Real.sqrt K) / N :=
      div_le_div_of_nonneg_right htotal hN0.le
    _ = 50 * ((K : ℝ) / N) + 64 * Real.sqrt ((K : ℝ) / N) := by
      rw [Real.sqrt_div (Nat.cast_nonneg K)]
      have hs0 : Real.sqrt (N : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hN0).ne'
      have hr : Real.sqrt (N : ℝ) / N = 1 / Real.sqrt N := by
        apply (div_eq_div_iff hN0.ne' hs0).mpr
        nlinarith only [Real.sq_sqrt hN0.le]
      calc
        _ = 50 * ((K : ℝ) / N) + 64 * Real.sqrt K * (Real.sqrt (N : ℝ) / N) := by ring
        _ = _ := by rw [hr]; ring

/-- Even after multiplication by the overlap logarithm, the polar Gram row defect vanishes in ℓ². -/
theorem tendsto_log_scaled_poleRowDefect_sq
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R)) :
    Tendsto (fun N : ℕ => (Real.log (c N) / c N) ^ 2 *
      ∑ n ∈ Icc 1 N, poleRowDefect tiltedUnitSpline (c N) N n ^ 2) atTop (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ := exists_sum_poleRowDefect_sq_le contDiff_tiltedUnitSpline
    tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos
  have hcinf := (criticalCurve_facts hc hR hcrit).1
  have hwidth : Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0) := by
    simpa only [pow_one, pow_zero, mul_one] using criticalCurve_pow_log_div_natCast hc hR hcrit 1 0
  have hlim : Tendsto (fun N : ℕ => 48 * C / c N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hcinf
  refine squeeze_zero' (Eventually.of_forall fun N =>
    mul_nonneg (sq_nonneg _) (sum_nonneg fun _ _ => sq_nonneg _)) ?_ hlim
  filter_upwards [eventually_below_overlap_pair_admissible hc hR hcrit,
    hwidth.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 8)),
    eventually_ge_atTop 1] with N hadm hw hN1
  have hc0 : 0 < c N := zero_lt_one.trans_le (hc N)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  obtain ⟨_, _, _, hc4⟩ := hadm 1 1 (by simpa using hc N) (by simpa using hc N)
  have h8 : 8 * c N ≤ N := by
    have hh := (div_lt_iff₀ hN0).mp hw
    linarith only [hh]
  have hsq := log_sq_le_sixteen_sqrt (hc N)
  have hlog := Real.log_le_rpow_div hc0.le (by norm_num : (0 : ℝ) < 1 / 2)
  rw [← Real.sqrt_eq_rpow] at hlog
  norm_num at hlog
  have hsqrt : 1 ≤ Real.sqrt (c N) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (hc N)
  have hlog3 : 1 + Real.log (c N) ≤ 3 * Real.sqrt (c N) := by
    linarith only [hlog, hsqrt]
  have hprod : Real.log (c N) ^ 2 * (1 + Real.log (c N)) ≤ 48 * c N := by
    have hp := mul_le_mul hsq hlog3
      (by have := Real.log_nonneg (hc N); positivity) (by positivity)
    have he : (16 * Real.sqrt (c N)) * (3 * Real.sqrt (c N)) = 48 * c N := by
      nlinarith only [Real.sq_sqrt hc0.le]
    exact hp.trans_eq he
  calc
    _ ≤ (Real.log (c N) / c N) ^ 2 * (C * (1 + Real.log (c N))) :=
      mul_le_mul_of_nonneg_left (hbound (hc N) h8 hc4) (sq_nonneg _)
    _ = C * (Real.log (c N) ^ 2 * (1 + Real.log (c N))) / c N ^ 2 := by ring
    _ ≤ C * (48 * c N) / c N ^ 2 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hprod hC) (sq_nonneg _)
    _ = _ := by field_simp [hc0.ne']

#print axioms normalized_sum_terminal_polarCenterRow_sq_le
#print axioms tendsto_log_scaled_poleRowDefect_sq
end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
