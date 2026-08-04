import GaloisForLFunctions.RHTower.Sieve.LogLogTelescope

/-!
# The harmonic sum over a dyadic block

The fibre decomposition weights each outer factor `a` by the length `h√x/a` of its fibre, so the
trivial size of the balanced pair sum is `h√x · ∑_{a ∈ block} 1/a`.  Over a dyadic block that sum
converges to `log 2`, which is exactly the normalising constant of the bilinear all-interval
theorem.

The two sides are the telescoped forms of the concavity of the logarithm:

    log(n+1) − log m  ≤  ∑_{m ≤ k ≤ n} 1/k  ≤  log n − log(m−1),

and at `m = ⌈u⌉`, `n = ⌊2u⌋` both ends tend to `log 2`.
-/

namespace RHTower.Sieve

open Finset Filter Topology

/-- The reciprocal tends to zero. -/
theorem tendsto_one_div_atTop : Tendsto (fun u : ℝ => 1 / u) atTop (𝓝 0) := by
  simpa [one_div] using tendsto_inv_atTop_zero

/-- **The harmonic sum over an interval, upper form.** -/
theorem sum_Icc_one_div_le_log_sub {m n : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n + 1) :
    ∑ k ∈ Finset.Icc m n, 1 / (k : ℝ) ≤ Real.log n - Real.log ((m : ℝ) - 1) := by
  classical
  have hIcc : Finset.Icc m n = Finset.Ico m (n + 1) := rfl
  have hterm : ∀ k ∈ Finset.Ico m (n + 1),
      1 / (k : ℝ) ≤ Real.log (((k + 1 : ℕ) : ℝ) - 1) - Real.log ((k : ℝ) - 1) := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    have hk2 : 2 ≤ k := le_trans hm hk.1
    have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
    have hpos : (0 : ℝ) < (k : ℝ) - 1 := by linarith
    have hle : (k : ℝ) - 1 ≤ (k : ℝ) := by linarith
    have hstep := le_log_sub_log hpos hle
    have hcast : (((k + 1 : ℕ) : ℝ) - 1) = (k : ℝ) := by push_cast; ring
    rw [hcast]
    have hval : ((k : ℝ) - ((k : ℝ) - 1)) / (k : ℝ) = 1 / (k : ℝ) := by
      congr 1
      ring
    linarith [hval ▸ hstep]
  have hsum := Finset.sum_le_sum hterm
  rw [hIcc]
  refine le_trans hsum (le_of_eq ?_)
  have htel := sum_Ico_telescope (fun i : ℕ => Real.log ((i : ℝ) - 1)) (m := m) (N := n + 1)
    (by omega)
  rw [htel]
  congr 1
  push_cast
  norm_num

/-- **The harmonic sum over an interval, lower form.** -/
theorem log_sub_le_sum_Icc_one_div {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n + 1) :
    Real.log ((n : ℝ) + 1) - Real.log m ≤ ∑ k ∈ Finset.Icc m n, 1 / (k : ℝ) := by
  classical
  have hIcc : Finset.Icc m n = Finset.Ico m (n + 1) := rfl
  have hterm : ∀ k ∈ Finset.Ico m (n + 1),
      Real.log (((k + 1 : ℕ) : ℝ)) - Real.log ((k : ℝ)) ≤ 1 / (k : ℝ) := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    have hk1 : 1 ≤ k := le_trans hm hk.1
    have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    have hpos : (0 : ℝ) < (k : ℝ) := by linarith
    have hle : (k : ℝ) ≤ (k : ℝ) + 1 := by linarith
    have hstep := log_sub_log_le hpos hle
    have hcast : (((k + 1 : ℕ) : ℝ)) = (k : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    have hval : ((k : ℝ) + 1 - (k : ℝ)) / (k : ℝ) = 1 / (k : ℝ) := by
      congr 1
      ring
    linarith [hval ▸ hstep]
  have hsum := Finset.sum_le_sum hterm
  rw [hIcc]
  refine le_trans (le_of_eq ?_) hsum
  have htel := sum_Ico_telescope (fun i : ℕ => Real.log ((i : ℝ))) (m := m) (N := n + 1)
    (by omega)
  rw [htel]
  congr 1
  push_cast
  norm_num

/-- The floor of a doubled variable, normalised. -/
theorem tendsto_floor_two_mul_div :
    Tendsto (fun u : ℝ => ((⌊2 * u⌋₊ : ℝ)) / u) atTop (𝓝 2) := by
  have hlow : Tendsto (fun u : ℝ => (2 * u - 1) / u) atTop (𝓝 2) := by
    have hbase : Tendsto (fun u : ℝ => 2 - 1 / u) atTop (𝓝 2) := by
      have := tendsto_const_nhds (x := (2 : ℝ)) (f := (atTop : Filter ℝ)) |>.sub
        tendsto_one_div_atTop
      rwa [sub_zero] at this
    refine Tendsto.congr' ?_ hbase
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
    field_simp
  have hhigh : Tendsto (fun _ : ℝ => (2 : ℝ)) atTop (𝓝 2) := tendsto_const_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hhigh ?_ ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
    have hfl : 2 * u - 1 ≤ (⌊2 * u⌋₊ : ℝ) := by
      have := Nat.lt_floor_add_one (2 * u)
      linarith
    exact div_le_div_of_nonneg_right hfl hu.le
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
    have hfl : ((⌊2 * u⌋₊ : ℝ)) ≤ 2 * u := Nat.floor_le (by linarith)
    rw [div_le_iff₀ hu]
    linarith

/-- The ceiling, normalised. -/
theorem tendsto_ceil_div : Tendsto (fun u : ℝ => ((⌈u⌉₊ : ℝ)) / u) atTop (𝓝 1) := by
  have hlow : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hhigh : Tendsto (fun u : ℝ => (u + 1) / u) atTop (𝓝 1) := by
    have hbase : Tendsto (fun u : ℝ => 1 + 1 / u) atTop (𝓝 1) := by
      have := tendsto_const_nhds (x := (1 : ℝ)) (f := (atTop : Filter ℝ)) |>.add
        tendsto_one_div_atTop
      rwa [add_zero] at this
    refine Tendsto.congr' ?_ hbase
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
    field_simp
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hhigh ?_ ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
    rw [le_div_iff₀ hu, one_mul]
    exact Nat.le_ceil u
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
    have hce : ((⌈u⌉₊ : ℝ)) ≤ u + 1 := (Nat.ceil_lt_add_one hu.le).le
    exact div_le_div_of_nonneg_right hce hu.le

/-- The ceiling shifted down, normalised. -/
theorem tendsto_ceil_sub_one_div :
    Tendsto (fun u : ℝ => ((⌈u⌉₊ : ℝ) - 1) / u) atTop (𝓝 1) := by
  have hbase : Tendsto (fun u : ℝ => ((⌈u⌉₊ : ℝ)) / u - 1 / u) atTop (𝓝 1) := by
    have := tendsto_ceil_div.sub tendsto_one_div_atTop
    rwa [sub_zero] at this
  refine Tendsto.congr' ?_ hbase
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
  field_simp

/-- The floor of a doubled variable, shifted up and normalised. -/
theorem tendsto_floor_two_mul_add_one_div :
    Tendsto (fun u : ℝ => ((⌊2 * u⌋₊ : ℝ) + 1) / u) atTop (𝓝 2) := by
  have hbase : Tendsto (fun u : ℝ => ((⌊2 * u⌋₊ : ℝ)) / u + 1 / u) atTop (𝓝 2) := by
    have := tendsto_floor_two_mul_div.add tendsto_one_div_atTop
    rwa [add_zero] at this
  refine Tendsto.congr' ?_ hbase
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
  field_simp

/-- The upper end of the sandwich tends to `log 2`. -/
theorem tendsto_log_floor_sub_log_ceil_sub_one :
    Tendsto (fun u : ℝ => Real.log ((⌊2 * u⌋₊ : ℝ)) - Real.log ((⌈u⌉₊ : ℝ) - 1))
      atTop (𝓝 (Real.log 2)) := by
  have hratio : Tendsto
      (fun u : ℝ => (((⌊2 * u⌋₊ : ℝ)) / u) / (((⌈u⌉₊ : ℝ) - 1) / u)) atTop (𝓝 2) := by
    have hd := tendsto_floor_two_mul_div.div tendsto_ceil_sub_one_div one_ne_zero
    rwa [show (2 : ℝ) / 1 = 2 by norm_num] at hd
  have hlog : Tendsto
      (fun u : ℝ => Real.log ((((⌊2 * u⌋₊ : ℝ)) / u) / (((⌈u⌉₊ : ℝ) - 1) / u)))
      atTop (𝓝 (Real.log 2)) :=
    (Real.continuousAt_log (by norm_num)).tendsto.comp hratio
  refine hlog.congr' ?_
  filter_upwards [eventually_gt_atTop (4 : ℝ)] with u hu
  have hu0 : (0 : ℝ) < u := by linarith
  have hce : (1 : ℝ) < (⌈u⌉₊ : ℝ) - 1 := by
    have : u ≤ (⌈u⌉₊ : ℝ) := Nat.le_ceil u
    linarith
  have hfl : (0 : ℝ) < ((⌊2 * u⌋₊ : ℝ)) := by
    have := Nat.lt_floor_add_one (2 * u)
    linarith
  have hid : ((⌊2 * u⌋₊ : ℝ)) / u / (((⌈u⌉₊ : ℝ) - 1) / u)
      = ((⌊2 * u⌋₊ : ℝ)) / ((⌈u⌉₊ : ℝ) - 1) := by
    field_simp
  rw [hid, Real.log_div (ne_of_gt hfl) (by linarith)]

/-- The lower end of the sandwich tends to `log 2`. -/
theorem tendsto_log_floor_add_one_sub_log_ceil :
    Tendsto (fun u : ℝ => Real.log (((⌊2 * u⌋₊ : ℝ)) + 1) - Real.log ((⌈u⌉₊ : ℝ)))
      atTop (𝓝 (Real.log 2)) := by
  have hratio : Tendsto
      (fun u : ℝ => ((((⌊2 * u⌋₊ : ℝ)) + 1) / u) / (((⌈u⌉₊ : ℝ)) / u)) atTop (𝓝 2) := by
    have hd := tendsto_floor_two_mul_add_one_div.div tendsto_ceil_div one_ne_zero
    rwa [show (2 : ℝ) / 1 = 2 by norm_num] at hd
  have hlog : Tendsto
      (fun u : ℝ => Real.log (((((⌊2 * u⌋₊ : ℝ)) + 1) / u) / (((⌈u⌉₊ : ℝ)) / u)))
      atTop (𝓝 (Real.log 2)) :=
    (Real.continuousAt_log (by norm_num)).tendsto.comp hratio
  refine hlog.congr' ?_
  filter_upwards [eventually_gt_atTop (4 : ℝ)] with u hu
  have hu0 : (0 : ℝ) < u := by linarith
  have hce : (0 : ℝ) < (⌈u⌉₊ : ℝ) := by
    have : u ≤ (⌈u⌉₊ : ℝ) := Nat.le_ceil u
    linarith
  have hfl : (0 : ℝ) < ((⌊2 * u⌋₊ : ℝ)) + 1 := by
    have : (0 : ℝ) ≤ ((⌊2 * u⌋₊ : ℝ)) := by positivity
    linarith
  have hid : (((⌊2 * u⌋₊ : ℝ)) + 1) / u / (((⌈u⌉₊ : ℝ)) / u)
      = (((⌊2 * u⌋₊ : ℝ)) + 1) / ((⌈u⌉₊ : ℝ)) := by
    field_simp
  rw [hid, Real.log_div (ne_of_gt hfl) (ne_of_gt hce)]

/-- **The harmonic sum over a dyadic block tends to `log 2`.** -/
theorem tendsto_sum_dyadic_one_div :
    Tendsto (fun u : ℝ => ∑ k ∈ Finset.Icc ⌈u⌉₊ ⌊2 * u⌋₊, 1 / (k : ℝ))
      atTop (𝓝 (Real.log 2)) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_log_floor_add_one_sub_log_ceil tendsto_log_floor_sub_log_ceil_sub_one ?_ ?_
  · filter_upwards [eventually_gt_atTop (4 : ℝ)] with u hu
    have hu0 : (0 : ℝ) < u := by linarith
    have hm1 : 1 ≤ ⌈u⌉₊ := Nat.one_le_ceil_iff.2 hu0
    have hmn : ⌈u⌉₊ ≤ ⌊2 * u⌋₊ + 1 := by
      have hce : ((⌈u⌉₊ : ℝ)) ≤ u + 1 := (Nat.ceil_lt_add_one hu0.le).le
      have hfl : 2 * u - 1 ≤ ((⌊2 * u⌋₊ : ℝ)) := by
        have := Nat.lt_floor_add_one (2 * u)
        linarith
      have : ((⌈u⌉₊ : ℝ)) ≤ ((⌊2 * u⌋₊ : ℝ)) + 1 := by linarith
      exact_mod_cast this
    have hbase := log_sub_le_sum_Icc_one_div hm1 hmn
    exact hbase
  · filter_upwards [eventually_gt_atTop (4 : ℝ)] with u hu
    have hu0 : (0 : ℝ) < u := by linarith
    have hm2 : 2 ≤ ⌈u⌉₊ := by
      have : (2 : ℝ) ≤ u := by linarith
      have hle : u ≤ ((⌈u⌉₊ : ℝ)) := Nat.le_ceil u
      have : (2 : ℝ) ≤ ((⌈u⌉₊ : ℝ)) := by linarith
      exact_mod_cast this
    have hmn : ⌈u⌉₊ ≤ ⌊2 * u⌋₊ + 1 := by
      have hce : ((⌈u⌉₊ : ℝ)) ≤ u + 1 := (Nat.ceil_lt_add_one hu0.le).le
      have hfl : 2 * u - 1 ≤ ((⌊2 * u⌋₊ : ℝ)) := by
        have := Nat.lt_floor_add_one (2 * u)
        linarith
      have : ((⌈u⌉₊ : ℝ)) ≤ ((⌊2 * u⌋₊ : ℝ)) + 1 := by linarith
      exact_mod_cast this
    exact sum_Icc_one_div_le_log_sub hm2 hmn

/-- **A ratio of two quantities of linear growth has a logarithmic limit.** -/
theorem tendsto_log_sub_log_of_ratio {A B : ℝ → ℝ} {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hA : Tendsto (fun u => A u / u) atTop (𝓝 a)) (hB : Tendsto (fun u => B u / u) atTop (𝓝 b))
    (hApos : ∀ᶠ u in atTop, 0 < A u) (hBpos : ∀ᶠ u in atTop, 0 < B u) :
    Tendsto (fun u => Real.log (B u) - Real.log (A u)) atTop (𝓝 (Real.log (b / a))) := by
  have hratio : Tendsto (fun u => (B u / u) / (A u / u)) atTop (𝓝 (b / a)) :=
    hB.div hA (ne_of_gt ha)
  have hlog : Tendsto (fun u => Real.log ((B u / u) / (A u / u))) atTop (𝓝 (Real.log (b / a))) :=
    (Real.continuousAt_log (by positivity)).tendsto.comp hratio
  refine Tendsto.congr' ?_ hlog
  filter_upwards [eventually_gt_atTop (0 : ℝ), hApos, hBpos] with u hu hAu hBu
  have hid : (B u / u) / (A u / u) = B u / A u := by
    field_simp
  rw [hid, Real.log_div (ne_of_gt hBu) (ne_of_gt hAu)]

/-- **The harmonic sum over a block of ratio two.**  Only the normalised growth of the endpoints
matters. -/
theorem tendsto_sum_Icc_one_div_of_ratio {p q : ℝ → ℕ}
    (hp : Tendsto (fun u => ((p u : ℝ)) / u) atTop (𝓝 1))
    (hq : Tendsto (fun u => ((q u : ℝ)) / u) atTop (𝓝 2))
    (hp2 : ∀ᶠ u in atTop, 2 ≤ p u) (hpq : ∀ᶠ u in atTop, p u ≤ q u + 1) :
    Tendsto (fun u => ∑ k ∈ Finset.Icc (p u) (q u), 1 / (k : ℝ)) atTop (𝓝 (Real.log 2)) := by
  have hone : Tendsto (fun u : ℝ => 1 / u) atTop (𝓝 0) := tendsto_one_div_atTop
  have hpsub : Tendsto (fun u => ((p u : ℝ) - 1) / u) atTop (𝓝 1) := by
    have hbase : Tendsto (fun u => ((p u : ℝ)) / u - 1 / u) atTop (𝓝 1) := by
      have := hp.sub hone
      rwa [sub_zero] at this
    refine Tendsto.congr' ?_ hbase
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
    field_simp
  have hqadd : Tendsto (fun u => ((q u : ℝ) + 1) / u) atTop (𝓝 2) := by
    have hbase : Tendsto (fun u => ((q u : ℝ)) / u + 1 / u) atTop (𝓝 2) := by
      have := hq.add hone
      rwa [add_zero] at this
    refine Tendsto.congr' ?_ hbase
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
    field_simp
  have hq1 : ∀ᶠ u in atTop, 1 ≤ q u := by
    filter_upwards [hp2, hpq] with u h2 hle
    omega
  have hAup : ∀ᶠ u in atTop, (0 : ℝ) < (p u : ℝ) - 1 := by
    filter_upwards [hp2] with u h2
    have : (2 : ℝ) ≤ (p u : ℝ) := by exact_mod_cast h2
    linarith
  have hBup : ∀ᶠ u in atTop, (0 : ℝ) < ((q u : ℝ)) := by
    filter_upwards [hq1] with u h1
    have : (1 : ℝ) ≤ (q u : ℝ) := by exact_mod_cast h1
    linarith
  have hAlow : ∀ᶠ u in atTop, (0 : ℝ) < ((p u : ℝ)) := by
    filter_upwards [hp2] with u h2
    have : (2 : ℝ) ≤ (p u : ℝ) := by exact_mod_cast h2
    linarith
  have hBlow : ∀ᶠ u in atTop, (0 : ℝ) < ((q u : ℝ) + 1) := by
    filter_upwards [hq1] with u h1
    have : (1 : ℝ) ≤ (q u : ℝ) := by exact_mod_cast h1
    linarith
  have hupper := tendsto_log_sub_log_of_ratio (a := 1) (b := 2) one_pos two_pos hpsub hq hAup hBup
  have hlower := tendsto_log_sub_log_of_ratio (a := 1) (b := 2) one_pos two_pos hp hqadd hAlow hBlow
  rw [show (2 : ℝ) / 1 = 2 by norm_num] at hupper hlower
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper ?_ ?_
  · filter_upwards [hp2, hpq] with u h2 hle
    have hm1 : 1 ≤ p u := by omega
    have := log_sub_le_sum_Icc_one_div (m := p u) (n := q u) hm1 hle
    have hcast : ((q u : ℝ)) + 1 = ((q u : ℕ) : ℝ) + 1 := rfl
    exact this
  · filter_upwards [hp2, hpq] with u h2 hle
    exact sum_Icc_one_div_le_log_sub (m := p u) (n := q u) h2 hle

end RHTower.Sieve
