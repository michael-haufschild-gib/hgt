import GaloisForLFunctions.RHTower.Sieve.PrimeWindowDyadic

/-!
# The prime tail above an abscissa

Summing the dyadic windows `(2^k z, 2^{k+1} z]` bounds the tail

    ∑_{p > z} p^{−σ}  ≤  ((log 2 + 2C)/log z) · ∑_{k} 2^{−k(σ−1)},

because on the `k`-th window `p^{−σ} = p^{−1}·p^{−(σ−1)} ≤ p^{−1}(2^k z)^{−(σ−1)}` and the
reciprocal sum of the window is at most `(log 2 + 2C)/log z`.  The geometric factor is controlled by
`1 − 2^{−(σ−1)} ≥ (σ−1)log 2/2`, so the whole tail is at most `2(log 2 + 2C)/((σ−1) log z · log 2)`.

At the standard `σ = 1 + 1/log z` that is the constant `2(log 2 + 2C)/log 2`, uniformly in `z`.
-/

namespace RHTower.Sieve

open Finset

/-- A prime window splits at an interior point. -/
theorem bigPrimeSet_split {a m b : ℕ} (ham : a ≤ m) (hmb : m ≤ b) :
    bigPrimeSet a b = bigPrimeSet a m ∪ bigPrimeSet m b := by
  classical
  rw [bigPrimeSet, bigPrimeSet, bigPrimeSet, ← Finset.filter_union]
  congr 1
  ext n
  simp only [Finset.mem_Icc, Finset.mem_union]
  omega

/-- The two halves of a split window are disjoint. -/
theorem bigPrimeSet_split_disjoint (a m b : ℕ) :
    Disjoint (bigPrimeSet a m) (bigPrimeSet m b) := by
  classical
  rw [Finset.disjoint_left]
  intro n hn hn'
  rw [bigPrimeSet, Finset.mem_filter, Finset.mem_Icc] at hn hn'
  omega

/-- **The dyadic block bound.** -/
theorem sum_rpow_dyadic_block_le {y : ℕ} (hy : 2 ≤ y) {σ : ℝ} (hσ : 1 < σ) :
    ∑ p ∈ bigPrimeSet y (2 * y), ((p : ℝ)) ^ (-σ)
      ≤ ((y : ℝ)) ^ (-(σ - 1))
        * ((Real.log 2 + 2 * (2 * mertensFirstConst + 1 / 2)) / Real.log y) := by
  classical
  have hy2 : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hy0 : (0 : ℝ) < (y : ℝ) := by linarith
  have hpow0 : (0 : ℝ) < ((y : ℝ)) ^ (-(σ - 1)) := Real.rpow_pos_of_pos hy0 _
  have hterm : ∀ p ∈ bigPrimeSet y (2 * y),
      ((p : ℝ)) ^ (-σ) ≤ ((y : ℝ)) ^ (-(σ - 1)) * (1 / (p : ℝ)) := by
    intro p hp
    rw [bigPrimeSet, Finset.mem_filter, Finset.mem_Icc] at hp
    obtain ⟨⟨hlow, -⟩, -⟩ := hp
    have hpy : (y : ℝ) ≤ (p : ℝ) := by
      have : y ≤ p := by omega
      exact_mod_cast this
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
    have hsplit : ((p : ℝ)) ^ (-σ) = ((p : ℝ)) ^ (-(σ - 1)) * ((p : ℝ)) ^ (-1 : ℝ) := by
      rw [← Real.rpow_add hp0]
      congr 1
      ring
    have hbase : ((y : ℝ)) ^ (σ - 1) ≤ ((p : ℝ)) ^ (σ - 1) :=
      Real.rpow_le_rpow hy0.le hpy (by linarith)
    have hmono : ((p : ℝ)) ^ (-(σ - 1)) ≤ ((y : ℝ)) ^ (-(σ - 1)) := by
      rw [Real.rpow_neg hp0.le, Real.rpow_neg hy0.le]
      exact inv_anti₀ (Real.rpow_pos_of_pos hy0 _) hbase
    have hinv : ((p : ℝ)) ^ (-1 : ℝ) = 1 / (p : ℝ) := by
      rw [Real.rpow_neg_one, one_div]
    rw [hsplit, hinv]
    exact mul_le_mul_of_nonneg_right hmono (by positivity)
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ hpow0.le
  exact sum_inv_dyadic_window_le hy

/-- **The tail over a dyadic tower.** -/
theorem sum_rpow_bigPrimeSet_pow_le {z : ℕ} (hz : 2 ≤ z) {σ : ℝ} (hσ : 1 < σ) (K : ℕ) :
    ∑ p ∈ bigPrimeSet z (2 ^ K * z), ((p : ℝ)) ^ (-σ)
      ≤ ∑ k ∈ Finset.range K,
          (((2 ^ k * z : ℕ) : ℝ)) ^ (-(σ - 1))
            * ((Real.log 2 + 2 * (2 * mertensFirstConst + 1 / 2))
              / Real.log ((2 ^ k * z : ℕ) : ℝ)) := by
  classical
  induction K with
  | zero =>
      have hempty : bigPrimeSet z (2 ^ 0 * z) = ∅ := by
        rw [bigPrimeSet]
        refine Finset.filter_eq_empty_iff.2 ?_
        intro n hn
        rw [Finset.mem_Icc] at hn
        omega
      rw [hempty]
      simp
  | succ K ih =>
      have hzK : 2 ≤ 2 ^ K * z := by
        have h1 : 1 ≤ 2 ^ K := Nat.one_le_two_pow
        nlinarith
      have hle1 : z ≤ 2 ^ K * z := by
        have h1 : 1 ≤ 2 ^ K := Nat.one_le_two_pow
        nlinarith
      have hle2 : 2 ^ K * z ≤ 2 ^ (K + 1) * z := by
        have : (2 : ℕ) ^ K ≤ 2 ^ (K + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        nlinarith
      have hsplit := bigPrimeSet_split hle1 hle2
      have hdisj := bigPrimeSet_split_disjoint z (2 ^ K * z) (2 ^ (K + 1) * z)
      rw [hsplit, Finset.sum_union hdisj]
      have hdouble : (2 : ℕ) ^ (K + 1) * z = 2 * (2 ^ K * z) := by ring
      rw [hdouble]
      have hblock := sum_rpow_dyadic_block_le (y := 2 ^ K * z) hzK hσ
      rw [Finset.sum_range_succ]
      linarith [ih, hblock]

/-- The dyadic weight is a geometric ratio. -/
theorem rpow_two_pow_mul {z : ℕ} (hz : 2 ≤ z) {σ : ℝ} (hσ : 1 < σ) (k : ℕ) :
    (((2 ^ k * z : ℕ) : ℝ)) ^ (-(σ - 1))
      ≤ (((2 : ℝ)) ^ (-(σ - 1))) ^ k := by
  have hz1 : (1 : ℝ) ≤ (z : ℝ) := by
    have : (2 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
    linarith
  have hcast : (((2 ^ k * z : ℕ) : ℝ)) = ((2 : ℝ)) ^ k * (z : ℝ) := by push_cast; ring
  rw [hcast, Real.mul_rpow (by positivity) (by linarith)]
  have hz0 : ((z : ℝ)) ^ (-(σ - 1)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hz1 (by linarith)
  have hpow : (((2 : ℝ)) ^ k) ^ (-(σ - 1)) = (((2 : ℝ)) ^ (-(σ - 1))) ^ k := by
    rw [← Real.rpow_natCast ((2 : ℝ)) k, ← Real.rpow_mul (by norm_num),
      ← Real.rpow_natCast (((2 : ℝ)) ^ (-(σ - 1))) k, ← Real.rpow_mul (by norm_num)]
    congr 1
    ring
  rw [hpow]
  have hbase : (0 : ℝ) ≤ (((2 : ℝ)) ^ (-(σ - 1))) ^ k := by positivity
  nlinarith [hz0, hbase]

/-- **The prime tail above an abscissa.**  Uniform in the truncation. -/
theorem sum_rpow_bigPrimeSet_le_const {z : ℕ} (hz : 2 ≤ z) {σ : ℝ} (hσ : 1 < σ)
    (hσ1 : σ - 1 ≤ 1) (K : ℕ) :
    ∑ p ∈ bigPrimeSet z (2 ^ K * z), ((p : ℝ)) ^ (-σ)
      ≤ (Real.log 2 + 2 * (2 * mertensFirstConst + 1 / 2)) / Real.log z
        * (2 / ((σ - 1) * Real.log 2)) := by
  classical
  set A : ℝ := Real.log 2 + 2 * (2 * mertensFirstConst + 1 / 2) with hA
  have hA0 : (0 : ℝ) ≤ A := by
    have h1 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have h2 := mertensFirstConst_nonneg
    rw [hA]; linarith
  have hz2 : (2 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
  have hlogz : (0 : ℝ) < Real.log (z : ℝ) := Real.log_pos (by linarith)
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set r : ℝ := ((2 : ℝ)) ^ (-(σ - 1)) with hr
  have hr0 : (0 : ℝ) < r := Real.rpow_pos_of_pos (by norm_num) _
  have hrexp : r = Real.exp (-((σ - 1) * Real.log 2)) := by
    rw [hr, Real.rpow_def_of_pos (by norm_num)]
    congr 1
    ring
  have hu0 : (0 : ℝ) ≤ (σ - 1) * Real.log 2 := by
    have : (0 : ℝ) ≤ σ - 1 := by linarith
    positivity
  have hu1 : (σ - 1) * Real.log 2 ≤ 1 := by
    have hl : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    nlinarith [hu0]
  have hgap : (σ - 1) * Real.log 2 / 2 ≤ 1 - r := by
    rw [hrexp]
    exact one_sub_exp_neg_ge hu0 hu1
  have hrlt : r < 1 := by
    have hpos : (0 : ℝ) < (σ - 1) * Real.log 2 / 2 := by
      have : (0 : ℝ) < σ - 1 := by linarith
      positivity
    linarith
  -- termwise collapse
  have hterm : ∀ k ∈ Finset.range K,
      (((2 ^ k * z : ℕ) : ℝ)) ^ (-(σ - 1)) * (A / Real.log ((2 ^ k * z : ℕ) : ℝ))
        ≤ (A / Real.log (z : ℝ)) * r ^ k := by
    intro k _
    have hzk : 2 ≤ 2 ^ k * z := by
      have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      nlinarith
    have hzkR : (2 : ℝ) ≤ ((2 ^ k * z : ℕ) : ℝ) := by exact_mod_cast hzk
    have hlogk : Real.log (z : ℝ) ≤ Real.log ((2 ^ k * z : ℕ) : ℝ) := by
      refine Real.log_le_log (by linarith) ?_
      have : z ≤ 2 ^ k * z := by
        have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
        nlinarith
      exact_mod_cast this
    have hdiv : A / Real.log ((2 ^ k * z : ℕ) : ℝ) ≤ A / Real.log (z : ℝ) :=
      div_le_div_of_nonneg_left hA0 hlogz hlogk
    have hw := rpow_two_pow_mul hz hσ k
    have hw0 : (0 : ℝ) ≤ (((2 ^ k * z : ℕ) : ℝ)) ^ (-(σ - 1)) :=
      Real.rpow_nonneg (by linarith) _
    have hd0 : (0 : ℝ) ≤ A / Real.log ((2 ^ k * z : ℕ) : ℝ) := by
      have : (0 : ℝ) < Real.log ((2 ^ k * z : ℕ) : ℝ) := lt_of_lt_of_le hlogz hlogk
      positivity
    calc (((2 ^ k * z : ℕ) : ℝ)) ^ (-(σ - 1)) * (A / Real.log ((2 ^ k * z : ℕ) : ℝ))
        ≤ (((2 ^ k * z : ℕ) : ℝ)) ^ (-(σ - 1)) * (A / Real.log (z : ℝ)) :=
          mul_le_mul_of_nonneg_left hdiv hw0
      _ ≤ r ^ k * (A / Real.log (z : ℝ)) := by
          refine mul_le_mul_of_nonneg_right hw ?_
          positivity
      _ = (A / Real.log (z : ℝ)) * r ^ k := by ring
  refine le_trans (sum_rpow_bigPrimeSet_pow_le hz hσ K) ?_
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  have hgeom : ∑ k ∈ Finset.range K, r ^ k ≤ (1 - r)⁻¹ := by
    have hsummable : Summable (fun k : ℕ => r ^ k) := summable_geometric_of_lt_one hr0.le hrlt
    have hval : ∑' k : ℕ, r ^ k = (1 - r)⁻¹ := tsum_geometric_of_lt_one hr0.le hrlt
    rw [← hval]
    exact hsummable.sum_le_tsum _ (fun k _ => by positivity)
  have hinv : (1 - r)⁻¹ ≤ 2 / ((σ - 1) * Real.log 2) := by
    have hpos : (0 : ℝ) < (σ - 1) * Real.log 2 / 2 := by
      have : (0 : ℝ) < σ - 1 := by linarith
      positivity
    rw [show (2 : ℝ) / ((σ - 1) * Real.log 2) = ((σ - 1) * Real.log 2 / 2)⁻¹ by
      field_simp]
    exact inv_anti₀ hpos hgap
  have hcoef : (0 : ℝ) ≤ A / Real.log (z : ℝ) := by positivity
  calc (A / Real.log (z : ℝ)) * ∑ k ∈ Finset.range K, r ^ k
      ≤ (A / Real.log (z : ℝ)) * (1 - r)⁻¹ := mul_le_mul_of_nonneg_left hgeom hcoef
    _ ≤ (A / Real.log (z : ℝ)) * (2 / ((σ - 1) * Real.log 2)) :=
        mul_le_mul_of_nonneg_left hinv hcoef

/-- **The prime tail at the standard abscissa.**  With `σ = 1 + 1/log z` the tail is bounded by an
absolute constant, uniformly in `z` and in the truncation. -/
theorem sum_rpow_bigPrimeSet_le_abs {z : ℕ} (hz : 3 ≤ z) (K : ℕ) :
    ∑ p ∈ bigPrimeSet z (2 ^ K * z), ((p : ℝ)) ^ (-(1 + 1 / Real.log z))
      ≤ 2 * (Real.log 2 + 2 * (2 * mertensFirstConst + 1 / 2)) / Real.log 2 := by
  have hz3 : (3 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
  have hz2 : 2 ≤ z := by omega
  have hlogz : (1 : ℝ) ≤ Real.log (z : ℝ) := by
    have hexp : Real.exp 1 ≤ (z : ℝ) := by
      have := Real.exp_one_lt_d9
      linarith
    have := Real.log_le_log (Real.exp_pos 1) hexp
    rwa [Real.log_exp] at this
  have hlogz0 : (0 : ℝ) < Real.log (z : ℝ) := by linarith
  have hσ : (1 : ℝ) < 1 + 1 / Real.log (z : ℝ) := by
    have : (0 : ℝ) < 1 / Real.log (z : ℝ) := by positivity
    linarith
  have hσ1 : (1 + 1 / Real.log (z : ℝ)) - 1 ≤ 1 := by
    have : 1 / Real.log (z : ℝ) ≤ 1 := by
      rw [div_le_one hlogz0]
      exact hlogz
    linarith
  refine le_trans (sum_rpow_bigPrimeSet_le_const hz2 hσ hσ1 K) (le_of_eq ?_)
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hsub : (1 + 1 / Real.log (z : ℝ)) - 1 = 1 / Real.log (z : ℝ) := by ring
  rw [hsub]
  field_simp

end RHTower.Sieve
