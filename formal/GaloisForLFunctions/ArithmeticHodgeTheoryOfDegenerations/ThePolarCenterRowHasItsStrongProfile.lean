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
  exact htri.trans (by
    simp only [div_eq_mul_inv] at h1 h2 ⊢
    linarith only [h1, h2])


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
      one_mul, zero_div, sub_zero]
    have hln := Real.log_nonneg (show (1 : ℝ) ≤ N by exact_mod_cast hN1)
    simp only [Nat.sub_self, zero_add, Nat.cast_one, div_one, abs_one]
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
  have hmodel0 : 0 ≤ (N : ℝ) / n - Real.log (1 - ((n : ℝ) / N) ^ 2) / 2 :=
    sub_nonneg.mpr ((div_nonpos_of_nonpos_of_nonneg hlog0 (by norm_num)).trans (by positivity))
  rw [hmodel, abs_of_nonneg hmodel0]
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


/-- Splitting off the last `K` rows bounds the full top-window error by an interior reciprocal
error and a uniformly small endpoint tail. -/
lemma normalized_sum_polarCenter_error_le {δ : ℝ} (hδ : 0 < δ) {K N : ℕ}
    (hK1 : 1 ≤ K) (hK : 2 * K ≤ N) :
    (∑ n ∈ Ioc ⌊δ * (N : ℝ)⌋₊ N,
      (polarCenterRow N n - polarCenterProfile (fun _ => 1) ((n : ℝ) / N)) ^ 2) / N ≤
      (2 / (K : ℝ) + 1 / (δ * N)) ^ 2 +
        136 * ((K : ℝ) / N) + 256 * Real.sqrt ((K : ℝ) / N) := by
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK1
  let S := Ioc ⌊δ * (N : ℝ)⌋₊ N
  let E : ℕ → ℝ := fun n =>
    (polarCenterRow N n - polarCenterProfile (fun _ => 1) ((n : ℝ) / N)) ^ 2
  let C : ℝ := 2 / K + 1 / (δ * N)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hearly : ∀ n ∈ S, n ≤ N - K → E n ≤ C ^ 2 := by
    intro n hn hmid
    have hnlo : ⌊δ * (N : ℝ)⌋₊ < n := (mem_Ioc.mp hn).1
    have hn1 : 1 ≤ n := by omega
    have hnlt : n < N := by omega
    have hnδ : δ * (N : ℝ) < n := (Nat.lt_floor_add_one _).trans_le
      (by exact_mod_cast Nat.succ_le_of_lt hnlo)
    have hkn : K ≤ N - n := by omega
    have hab := abs_polarCenterRow_sub_profile_le hn1 hnlt
    have hrec₁ : 2 / ((N - n : ℕ) : ℝ) ≤ 2 / (K : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) hK0 (by exact_mod_cast hkn)
    have hrec₂ : 1 / (n : ℝ) ≤ 1 / (δ * N) :=
      one_div_le_one_div_of_le (mul_pos hδ hN0) hnδ.le
    have habC : |polarCenterRow N n - polarCenterProfile (fun _ => 1) ((n : ℝ) / N)| ≤ C := by
      exact hab.trans (add_le_add hrec₁ hrec₂)
    have hs := pow_le_pow_left₀ (abs_nonneg _) habC 2
    simpa only [E, sq_abs] using hs
  have hsplit : (∑ n ∈ S, E n) ≤ N * C ^ 2 + ∑ n ∈ Ioc (N - K) N, E n := by
    have hpoint : ∀ n ∈ S, E n ≤ C ^ 2 + if N - K < n then E n else 0 := by
      intro n hn
      by_cases hlate : N - K < n
      · rw [if_pos hlate]
        exact le_add_of_nonneg_left (sq_nonneg C)
      · rw [if_neg hlate, add_zero]
        exact hearly n hn (not_lt.mp hlate)
    have hsum := sum_le_sum hpoint
    rw [sum_add_distrib, sum_const, nsmul_eq_mul, ← sum_filter] at hsum
    have hcard : (S.card : ℝ) ≤ N := by
      dsimp only [S]
      rw [Nat.card_Ioc]
      exact_mod_cast Nat.sub_le N ⌊δ * (N : ℝ)⌋₊
    have hsub : S.filter (fun n => N - K < n) ⊆ Ioc (N - K) N := by
      intro n hn
      exact mem_Ioc.mpr ⟨(mem_filter.mp hn).2, (mem_Ioc.mp (mem_filter.mp hn).1).2⟩
    exact hsum.trans (add_le_add (mul_le_mul_of_nonneg_right hcard (sq_nonneg C))
      (sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by dsimp only [E]; positivity)))
  have htail : (∑ n ∈ Ioc (N - K) N, E n) / N ≤
      136 * ((K : ℝ) / N) + 256 * Real.sqrt ((K : ℝ) / N) := by
    have he : (∑ n ∈ Ioc (N - K) N, E n) ≤
        2 * (∑ n ∈ Ioc (N - K) N, polarCenterRow N n ^ 2) +
        2 * (∑ n ∈ Ioc (N - K) N, polarCenterProfile (fun _ => 1) ((n : ℝ) / N) ^ 2) := by
      rw [mul_sum, mul_sum, ← sum_add_distrib]
      exact sum_le_sum fun n _ => by
        dsimp only [E]
        nlinarith only [sq_nonneg (polarCenterRow N n + polarCenterProfile (fun _ => 1) ((n : ℝ) / N))]
    have hnorm := div_le_div_of_nonneg_right he hN0.le
    have h₁ := normalized_sum_terminal_polarCenterRow_sq_le hN1 hK
    have h₂ := normalized_sum_terminal_polarCenterProfile_sq_le hN1 hK
    have hid : (2 * (∑ n ∈ Ioc (N - K) N, polarCenterRow N n ^ 2) +
        2 * (∑ n ∈ Ioc (N - K) N, polarCenterProfile (fun _ => 1) ((n : ℝ) / N) ^ 2)) / N =
        2 * ((∑ n ∈ Ioc (N - K) N, polarCenterRow N n ^ 2) / N) +
        2 * ((∑ n ∈ Ioc (N - K) N, polarCenterProfile (fun _ => 1) ((n : ℝ) / N) ^ 2) / N) := by ring
    rw [hid] at hnorm
    linarith only [hnorm, h₁, h₂]
  have htotal := div_le_div_of_nonneg_right hsplit hN0.le
  have hid : ((N : ℝ) * C ^ 2 + ∑ n ∈ Ioc (N - K) N, E n) / N =
      C ^ 2 + (∑ n ∈ Ioc (N - K) N, E n) / N := by field_simp [hN0.ne']
  rw [hid] at htotal
  exact htotal.trans (by linarith only [htail])


/-- The polar harmonic center converges to its sampled logarithmic profile in normalized
square mean on every fixed terminal fraction of the horizon. -/
theorem tendsto_normalized_polarCenter_profile_error {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Ioc ⌊δ * (N : ℝ)⌋₊ N,
        (polarCenterRow N n - polarCenterProfile (fun _ => 1) ((n : ℝ) / N)) ^ 2) / N)
      atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall fun N => ha.trans_le
      (div_nonneg (sum_nonneg fun _ _ => sq_nonneg _) (Nat.cast_nonneg N))
  · intro ε hε
    let t := min (1 / 4 : ℝ) (ε / 1000)
    let η := t ^ 2
    have ht : 0 < t := lt_min (by norm_num) (by positivity)
    have ht1 : t ≤ 1 / 4 := min_le_left _ _
    have htε : t ≤ ε / 1000 := min_le_right _ _
    have hη : 0 < η := sq_pos_of_pos ht
    have hηt : η ≤ t := by dsimp only [η]; nlinarith only [ht, ht1]
    have hηhalf : η ≤ 1 / 2 := hηt.trans (ht1.trans (by norm_num))
    have htail : 136 * η + 256 * Real.sqrt η < ε / 2 := by
      have he : Real.sqrt η = t := Real.sqrt_sq ht.le
      rw [he]
      linarith only [hηt, htε, hε]
    let C : ℝ := 4 / η + 1 / δ
    have hC : 0 < C := by dsimp only [C]; positivity
    have hlim : Tendsto (fun N : ℕ => (C / (N : ℝ)) ^ 2) atTop (𝓝 0) := by
      have h := (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop :
        Tendsto (fun N : ℕ => C / (N : ℝ)) atTop (𝓝 0)).pow 2
      simpa only [zero_pow (by decide : 2 ≠ 0)] using h
    filter_upwards [eventually_ge_atTop 1,
      (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop).eventually_ge_atTop (4 / η),
      hlim.eventually (gt_mem_nhds (half_pos hε))] with N hN hlarge hsmall
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    let K := ⌊η * (N : ℝ)⌋₊
    have hηN : 4 ≤ η * (N : ℝ) := by
      have h := (div_le_iff₀ hη).mp hlarge
      simpa only [mul_comm] using h
    have hK1 : 1 ≤ K := Nat.le_floor (by norm_num only [Nat.cast_one]; linarith only [hηN])
    have hK0 : (0 : ℝ) < K := by exact_mod_cast hK1
    have hKhi : (K : ℝ) ≤ η * N := Nat.floor_le (mul_nonneg hη.le hN0.le)
    have hKlo : η * (N : ℝ) / 2 ≤ K := by
      have hh := Nat.sub_one_lt_floor (η * (N : ℝ))
      change η * (N : ℝ) - 1 < (K : ℝ) at hh
      linarith only [hh, hηN]
    have hKhalf : 2 * K ≤ N := by
      have hh := mul_le_mul_of_nonneg_right hηhalf hN0.le
      have hcast : 2 * (K : ℝ) ≤ N := by linarith only [hKhi, hh]
      exact_mod_cast hcast
    have hKr : (K : ℝ) / N ≤ η := (div_le_iff₀ hN0).mpr hKhi
    have hCbound : 2 / (K : ℝ) + 1 / (δ * N) ≤ C / N := by
      have hh := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2)
        (by positivity : 0 < η * (N : ℝ) / 2) hKlo
      calc
        _ ≤ 2 / (η * (N : ℝ) / 2) + 1 / (δ * N) := add_le_add hh le_rfl
        _ = C / N := by dsimp only [C]; field_simp [hη.ne', hδ.ne', hN0.ne']; ring
    have hCsq := pow_le_pow_left₀ (by positivity : 0 ≤ 2 / (K : ℝ) + 1 / (δ * N)) hCbound 2
    have htN : 136 * ((K : ℝ) / N) + 256 * Real.sqrt ((K : ℝ) / N) < ε / 2 :=
      (add_le_add (mul_le_mul_of_nonneg_left hKr (by norm_num))
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hKr) (by norm_num))).trans_lt htail
    have hbound := normalized_sum_polarCenter_error_le hδ hK1 hKhalf
    linarith only [hbound, hCsq, htN, hsmall]

#print axioms abs_polarCenterRow_sub_profile_le
#print axioms tendsto_normalized_polarCenter_profile_error
end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
