import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.PolarRowsHaveSummableTerminalTails

/-!
# The polar center row has its strong profile

Harmonic comparison gives uniform convergence away from the terminal endpoint;
squared logarithmic tail bounds control the rows approaching that endpoint.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Finset Filter Topology
open scoped BigOperators
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

/-- The exact harmonic center differs from its logarithmic profile by reciprocal distances
to the two endpoints. -/
theorem abs_polarCenterRow_sub_profile_le {N n : ℕ}
    (hn : 1 ≤ n) (hnN : n < N) :
    |polarCenterRow N n - polarCenterProfile (fun _ => 1) ((n : ℝ) / N)| ≤
      2 / ((N - n : ℕ) : ℝ) + 1 / (n : ℝ) := by
  have hN : 1 ≤ N := hn.trans hnN.le
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hk : 1 ≤ N - n := by omega
  have hk0 : (0 : ℝ) < (N - n : ℕ) := by exact_mod_cast hk
  have hp : 1 ≤ N + n := by omega
  have hp0 : (0 : ℝ) < (N + n : ℕ) := by exact_mod_cast hp
  let e : ℕ → ℝ := fun k => (harmonic k : ℝ) - Real.log k - Real.eulerMascheroniConstant
  have he (k : ℕ) (hk : 1 ≤ k) : |e k| ≤ 1 / (k : ℝ) :=
    HTGeometry.abs_harmonic_sub_log_sub_eulerMascheroni_le hk
  have hlog : Real.log (1 - ((n : ℝ) / N) ^ 2) =
      Real.log ((N - n : ℕ) : ℝ) + Real.log ((N + n : ℕ) : ℝ) - 2 * Real.log N := by
    have hid : 1 - ((n : ℝ) / N) ^ 2 =
        (((N - n : ℕ) : ℝ) * ((N + n : ℕ) : ℝ)) / (N : ℝ) ^ 2 := by
      rw [Nat.cast_sub hnN.le, Nat.cast_add]
      field_simp
      ring
    rw [hid, Real.log_div (mul_ne_zero hk0.ne' hp0.ne') (pow_ne_zero 2 hN0.ne'),
      Real.log_mul hk0.ne' hp0.ne', Real.log_pow]
    norm_num
  have hid : polarCenterRow N n - polarCenterProfile (fun _ => 1) ((n : ℝ) / N) =
      e N - e (N - n) / 2 - e (N + n) / 2 + 3 / (4 * (n : ℝ)) := by
    dsimp only [polarCenterRow, polarCenterProfile, e]
    rw [hlog]
    field_simp
    ring
  have hb2 : |e (N - n) / 2| ≤ (1 / ((N - n : ℕ) : ℝ)) / 2 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact div_le_div_of_nonneg_right (he _ hk) (by norm_num)
  have hb3 : |e (N + n) / 2| ≤ (1 / ((N + n : ℕ) : ℝ)) / 2 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact div_le_div_of_nonneg_right (he _ hp) (by norm_num)
  have hb4 : |3 / (4 * (n : ℝ))| ≤ 1 / n := by
    rw [abs_of_pos (by positivity : (0 : ℝ) < 3 / (4 * n))]
    calc
      _ = (3 / 4 : ℝ) / n := by ring
      _ ≤ 1 / n := div_le_div_of_nonneg_right (by norm_num) hn0.le
  have h1 : 1 / (N : ℝ) ≤ 1 / ((N - n : ℕ) : ℝ) :=
    one_div_le_one_div_of_le hk0 (by exact_mod_cast Nat.sub_le N n)
  have h2 : 1 / ((N + n : ℕ) : ℝ) ≤ 1 / ((N - n : ℕ) : ℝ) :=
    one_div_le_one_div_of_le hk0 (by exact_mod_cast (show N - n ≤ N + n by omega))
  rw [hid]
  have htri := (abs_add_le _ _).trans (add_le_add
    ((abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans (add_le_add (he N hN) hb2)) hb3)) hb4)
  exact htri.trans (by linarith only [h1, h2])


/-- The sampled logarithmic profile has the same summable terminal majorant as the exact row. -/
lemma abs_polarCenterProfile_one_le {N n : ℕ} (hn : n ∈ Icc 1 N) :
    |polarCenterProfile (fun _ => 1) ((n : ℝ) / N)| ≤ (N : ℝ) / n + 1 +
      Real.log ((N : ℝ) / (N - n + 1 : ℕ)) := by
  have hn1 := (mem_Icc.mp hn).1
  have hnN := (mem_Icc.mp hn).2
  have hN1 := hn1.trans hnN
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hk0 : (0 : ℝ) < (N - n + 1 : ℕ) := by positivity
  have hkN : N - n + 1 ≤ N := by omega
  have hratio : 0 ≤ Real.log ((N : ℝ) / (N - n + 1 : ℕ)) :=
    Real.log_nonneg ((le_div_iff₀ hk0).mpr (by
      simpa only [one_mul] using (show ((N - n + 1 : ℕ) : ℝ) ≤ N by exact_mod_cast hkN)))
  by_cases htop : n = N
  · subst n
    simp only [div_self hN0.ne', polarCenterProfile, one_pow, sub_self, Real.log_zero,
      one_mul, zero_div, sub_zero, abs_one]
    have hln := Real.log_nonneg (show (1 : ℝ) ≤ N by exact_mod_cast hN1)
    simp only [Nat.sub_self, zero_add, Nat.cast_one, div_one]
    linarith only [hln]
  have hnlt : n < N := lt_of_le_of_ne hnN htop
  have hk1 : 1 ≤ N - n := by omega
  have hx0 : 0 ≤ (n : ℝ) / N := by positivity
  have hx1 : (n : ℝ) / N < 1 := (div_lt_one hN0).mpr (by exact_mod_cast hnlt)
  have hy : 0 < 1 - ((n : ℝ) / N) ^ 2 := by
    nlinarith only [mul_pos (sub_pos.mpr hx1) (by positivity : 0 < 1 + (n : ℝ) / N)]
  have hy1 : 1 - ((n : ℝ) / N) ^ 2 ≤ 1 := by linarith only [sq_nonneg ((n : ℝ) / N)]
  have hlog0 := Real.log_nonpos hy.le hy1
  have hmodel : polarCenterProfile (fun _ => 1) ((n : ℝ) / N) =
      (N : ℝ) / n - Real.log (1 - ((n : ℝ) / N) ^ 2) / 2 := by
    unfold polarCenterProfile
    field_simp
  have hden : ((N - n + 1 : ℕ) : ℝ) / (2 * N) ≤ 1 - ((n : ℝ) / N) ^ 2 := by
    have hlin : ((N - n + 1 : ℕ) : ℝ) / (2 * N) ≤ ((N - n : ℕ) : ℝ) / N := by
      apply (div_le_div_iff₀ (by positivity) hN0).mpr
      have hk1R : (1 : ℝ) ≤ (N - n : ℕ) := by exact_mod_cast hk1
      push_cast
      nlinarith only [hk1R, hN0]
    have hcast : ((N - n : ℕ) : ℝ) / N = 1 - (n : ℝ) / N := by
      rw [Nat.cast_sub hnN]
      field_simp
    rw [hcast] at hlin
    exact hlin.trans (by nlinarith only [mul_nonneg hx0 (sub_nonneg.mpr hx1.le)])
  have hlog := Real.log_le_log (by positivity : 0 < ((N - n + 1 : ℕ) : ℝ) / (2 * N)) hden
  rw [Real.log_div hk0.ne' (by positivity : (2 * (N : ℝ)) ≠ 0),
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hN0.ne'] at hlog
  have hratio_eq : Real.log ((N : ℝ) / (N - n + 1 : ℕ)) =
      Real.log N - Real.log (N - n + 1 : ℕ) := Real.log_div hN0.ne' hk0.ne'
  have hlog2 : Real.log 2 ≤ 1 := by
    linarith only [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [hmodel, abs_of_nonneg (by have : 0 ≤ (N : ℝ) / n := by positivity; linarith only [this, hlog0])]
  linarith only [hlog, hratio_eq, hlog2, hratio]

/-- The logarithmic model has a uniformly small squared terminal tail. -/
lemma normalized_sum_terminal_polarCenterProfile_sq_le {K N : ℕ}
    (hN : 1 ≤ N) (hK : 2 * K ≤ N) :
    (∑ n ∈ Ioc (N - K) N, polarCenterProfile (fun _ => 1) ((n : ℝ) / N) ^ 2) / N ≤
      18 * ((K : ℝ) / N) + 64 * Real.sqrt ((K : ℝ) / N) := by
  have hKN : K ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hpt : ∀ n ∈ Ioc (N - K) N,
      polarCenterProfile (fun _ => 1) ((n : ℝ) / N) ^ 2 ≤
        18 + 2 * Real.log ((N : ℝ) / (N - n + 1 : ℕ)) ^ 2 := by
    intro n hn
    have hnN := (mem_Ioc.mp hn).2
    have hn1 : 1 ≤ n := by have := (mem_Ioc.mp hn).1; omega
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have htwo : N ≤ 2 * n := by have := (mem_Ioc.mp hn).1; omega
    have hr : (N : ℝ) / n ≤ 2 := (div_le_iff₀ hn0).mpr (by exact_mod_cast htwo)
    have hb := abs_polarCenterProfile_one_le (mem_Icc.mpr ⟨hn1, hnN⟩)
    have hab : |polarCenterProfile (fun _ => 1) ((n : ℝ) / N)| ≤
        3 + Real.log ((N : ℝ) / (N - n + 1 : ℕ)) := by linarith only [hb, hr]
    have hs := pow_le_pow_left₀ (abs_nonneg _) hab 2
    rw [sq_abs] at hs
    nlinarith only [hs, sq_nonneg (3 - Real.log ((N : ℝ) / (N - n + 1 : ℕ)))]
  have hsum := sum_le_sum hpt
  rw [sum_add_distrib, sum_const, ← mul_sum, Nat.card_Ioc, Nat.sub_sub_self hKN,
    nsmul_eq_mul, sum_terminal_log_ratio_sq_eq hKN] at hsum
  have hlog := sum_log_ratio_sq_le hKN
  have htotal : (∑ n ∈ Ioc (N - K) N, polarCenterProfile (fun _ => 1) ((n : ℝ) / N) ^ 2) ≤
      18 * K + 64 * Real.sqrt N * Real.sqrt K := by linarith only [hsum, hlog]
  calc
    _ ≤ (18 * K + 64 * Real.sqrt N * Real.sqrt K) / N :=
      div_le_div_of_nonneg_right htotal hN0.le
    _ = _ := by
      rw [Real.sqrt_div (Nat.cast_nonneg K)]
      have hs0 : Real.sqrt (N : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hN0).ne'
      have hr : Real.sqrt (N : ℝ) / N = 1 / Real.sqrt N := by
        apply (div_eq_div_iff hN0.ne' hs0).mpr
        nlinarith only [Real.sq_sqrt hN0.le]
      calc
        _ = 18 * ((K : ℝ) / N) + 64 * Real.sqrt K * (Real.sqrt (N : ℝ) / N) := by ring
        _ = _ := by rw [hr]; ring

#print axioms abs_polarCenterRow_sub_profile_le
end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
