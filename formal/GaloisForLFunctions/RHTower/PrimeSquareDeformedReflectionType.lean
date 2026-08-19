import GaloisForLFunctions.RHTower.PrimeSquareFourierStrata
import GaloisForLFunctions.RHTower.AdelicIntertwinerType

/-!
# Cofinal type of the critically normalized prime-square reflection

The critically normalized reflected-line coefficient `β_p(c)` of the deformed occupation line has
exact logarithmic type `|c|` in the prime: `log β_p(c) / log p → |c|`.  Weighted Cesàro summation
over the primes with the weights `log p` turns this into the cofinal exponential type

`log ∏_{p < N} β_p(c) / θ(N) → |c|`,

so the critically normalized scalar line comparison has type `exp(|c| θ(N))`, superessential
relative to the `exp(O(log N))` Wold–Gamma first-trace anomaly.
-/

open Filter Topology

namespace RHTower

noncomputable section

theorem criticalNormalizedReflection_neg (p : ℕ) (c : ℝ) :
    criticalNormalizedReflection p (-c) = criticalNormalizedReflection p c := by
  rw [criticalNormalizedReflection, criticalNormalizedReflection]
  have h1 : -(-c) = c := by ring
  have h2 : (2 : ℝ) * (-c) = -2 * c := by ring
  have h3 : (-2 : ℝ) * (-c) = 2 * c := by ring
  rw [h1, h2, h3]
  ring_nf

/-- Two-sided bound for the critically normalized reflection at positive drift. -/
theorem criticalNormalizedReflection_bounds {p : ℕ} (hp : 1 < p) {c : ℝ} (hc : 0 ≤ c)
    (hc2 : 2 * c ≤ 1) (hbig : 2 ≤ (p : ℝ) ^ c) :
    (p : ℝ) ^ c / 4 ≤ criticalNormalizedReflection p c ∧
      criticalNormalizedReflection p c ≤ 3 * (p : ℝ) ^ c := by
  have hpr : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hpc : (0 : ℝ) < (p : ℝ) ^ c := Real.rpow_pos_of_pos hp0 c
  have hpmc : (0 : ℝ) < (p : ℝ) ^ (-c) := Real.rpow_pos_of_pos hp0 (-c)
  have hp2c : (p : ℝ) ^ (2 * c) ≤ (p : ℝ) := by
    have h1 : (p : ℝ) ^ (2 * c) ≤ (p : ℝ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hpr.le hc2
    simpa using h1
  have hpm2c : (p : ℝ) ^ (-2 * c) ≤ 1 := by
    refine Real.rpow_le_one_of_one_le_of_nonpos hpr.le ?_
    linarith
  have hpm2c0 : (0 : ℝ) < (p : ℝ) ^ (-2 * c) := Real.rpow_pos_of_pos hp0 (-2 * c)
  have hp2c0 : (0 : ℝ) < (p : ℝ) ^ (2 * c) := Real.rpow_pos_of_pos hp0 (2 * c)
  -- numerator identities
  have hnum : (p : ℝ) * ((p : ℝ) ^ c + (p : ℝ) ^ (-c)) - ((p : ℝ) - 1)
      = (p : ℝ) * (p : ℝ) ^ c + (p : ℝ) * (p : ℝ) ^ (-c) - (p : ℝ) + 1 := by ring
  have hmc_le : (p : ℝ) ^ (-c) ≤ (p : ℝ) ^ c := by
    refine Real.rpow_le_rpow_of_exponent_le hpr.le ?_
    linarith
  have hNlower : (p : ℝ) * (p : ℝ) ^ c / 2
      ≤ (p : ℝ) * ((p : ℝ) ^ c + (p : ℝ) ^ (-c)) - ((p : ℝ) - 1) := by
    have hkey : (p : ℝ) ≤ (p : ℝ) * (p : ℝ) ^ c / 2 := by
      nlinarith [hbig, hp0]
    nlinarith [hpmc, hp0, hkey]
  have hNupper : (p : ℝ) * ((p : ℝ) ^ c + (p : ℝ) ^ (-c)) - ((p : ℝ) - 1)
      ≤ 3 * ((p : ℝ) * (p : ℝ) ^ c) := by
    have h1 : (1 : ℝ) ≤ (p : ℝ) * (p : ℝ) ^ c := by nlinarith [hpc, hpr]
    nlinarith [hmc_le, hp0, hpc]
  -- denominator bounds
  have hDsq : ((p : ℝ) + (p : ℝ) ^ (2 * c)) * ((p : ℝ) + (p : ℝ) ^ (-2 * c)) ≤ 4 * (p : ℝ) ^ 2 := by
    nlinarith [hp2c, hpm2c, hp0, hpr]
  have hDsq' : (p : ℝ) ^ 2
      ≤ ((p : ℝ) + (p : ℝ) ^ (2 * c)) * ((p : ℝ) + (p : ℝ) ^ (-2 * c)) := by
    nlinarith [hp2c0, hpm2c0, hp0]
  have hDpos : (0 : ℝ) < ((p : ℝ) + (p : ℝ) ^ (2 * c)) * ((p : ℝ) + (p : ℝ) ^ (-2 * c)) := by
    positivity
  have hDupper : Real.sqrt (((p : ℝ) + (p : ℝ) ^ (2 * c)) * ((p : ℝ) + (p : ℝ) ^ (-2 * c)))
      ≤ 2 * (p : ℝ) := by
    have h4 : (4 : ℝ) * (p : ℝ) ^ 2 = (2 * (p : ℝ)) ^ 2 := by ring
    calc Real.sqrt (((p : ℝ) + (p : ℝ) ^ (2 * c)) * ((p : ℝ) + (p : ℝ) ^ (-2 * c)))
        ≤ Real.sqrt (4 * (p : ℝ) ^ 2) := Real.sqrt_le_sqrt hDsq
      _ = 2 * (p : ℝ) := by
          rw [h4, Real.sqrt_sq (by positivity)]
  have hDlower : (p : ℝ)
      ≤ Real.sqrt (((p : ℝ) + (p : ℝ) ^ (2 * c)) * ((p : ℝ) + (p : ℝ) ^ (-2 * c))) := by
    calc (p : ℝ) = Real.sqrt ((p : ℝ) ^ 2) := (Real.sqrt_sq hp0.le).symm
      _ ≤ Real.sqrt (((p : ℝ) + (p : ℝ) ^ (2 * c)) * ((p : ℝ) + (p : ℝ) ^ (-2 * c))) :=
          Real.sqrt_le_sqrt hDsq'
  have hDpos' : (0 : ℝ)
      < Real.sqrt (((p : ℝ) + (p : ℝ) ^ (2 * c)) * ((p : ℝ) + (p : ℝ) ^ (-2 * c))) :=
    Real.sqrt_pos.mpr hDpos
  constructor
  · rw [criticalNormalizedReflection, le_div_iff₀ hDpos']
    calc (p : ℝ) ^ c / 4 * Real.sqrt (((p : ℝ) + (p : ℝ) ^ (2 * c)) * ((p : ℝ) + (p : ℝ) ^ (-2 * c)))
        ≤ (p : ℝ) ^ c / 4 * (2 * (p : ℝ)) := by
          refine mul_le_mul_of_nonneg_left hDupper (by positivity)
      _ = (p : ℝ) * (p : ℝ) ^ c / 2 := by ring
      _ ≤ (p : ℝ) * ((p : ℝ) ^ c + (p : ℝ) ^ (-c)) - ((p : ℝ) - 1) := hNlower
  · rw [criticalNormalizedReflection, div_le_iff₀ hDpos']
    calc (p : ℝ) * ((p : ℝ) ^ c + (p : ℝ) ^ (-c)) - ((p : ℝ) - 1)
        ≤ 3 * ((p : ℝ) * (p : ℝ) ^ c) := hNupper
      _ = 3 * (p : ℝ) ^ c * (p : ℝ) := by ring
      _ ≤ 3 * (p : ℝ) ^ c
          * Real.sqrt (((p : ℝ) + (p : ℝ) ^ (2 * c)) * ((p : ℝ) + (p : ℝ) ^ (-2 * c))) := by
          refine mul_le_mul_of_nonneg_left hDlower (by positivity)

/-- **The exact logarithmic type of the critically normalized reflection.** -/
theorem tendsto_log_criticalNormalizedReflection_div_log {c : ℝ} (hc0 : 0 ≤ c)
    (hc2 : 2 * c ≤ 1) :
    Tendsto (fun n : ℕ => Real.log (criticalNormalizedReflection n c) / Real.log n) atTop (𝓝 c) := by
  rcases eq_or_lt_of_le hc0 with hc | hc
  · -- zero drift: the normalized reflection is identically one
    have hzero : ∀ᶠ n : ℕ in atTop,
        Real.log (criticalNormalizedReflection n c) / Real.log n = 0 := by
      filter_upwards [eventually_gt_atTop 1] with n hn
      have hone : criticalNormalizedReflection n c = 1 :=
        (criticalNormalizedReflection_eq_one_iff hn c).mpr hc.symm
      rw [hone, Real.log_one, zero_div]
    have hEq : (fun n : ℕ => Real.log (criticalNormalizedReflection n c) / Real.log n)
        =ᶠ[atTop] (fun _ : ℕ => (0 : ℝ)) := hzero
    have hgoal : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 c) := by
      rw [← hc]
      exact tendsto_const_nhds
    exact Tendsto.congr' hEq.symm hgoal
  · -- positive drift: sandwich the logarithm
    have hbig : ∀ᶠ n : ℕ in atTop, 2 ≤ (n : ℝ) ^ c := by
      have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ c) atTop atTop := by
        have hcast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
          tendsto_natCast_atTop_atTop
        exact (tendsto_rpow_atTop hc).comp hcast
      exact hpow.eventually_ge_atTop 2
    have hlower : ∀ᶠ n : ℕ in atTop,
        c - Real.log 4 / Real.log n ≤ Real.log (criticalNormalizedReflection n c) / Real.log n := by
      filter_upwards [eventually_gt_atTop 1, hbig] with n hn hn2
      have hnr : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hlogpos : 0 < Real.log (n : ℝ) := Real.log_pos hnr
      have hbounds := criticalNormalizedReflection_bounds hn hc0 hc2 hn2
      have hpc : (0 : ℝ) < (n : ℝ) ^ c := Real.rpow_pos_of_pos (by linarith) c
      have hlog : Real.log ((n : ℝ) ^ c / 4) ≤ Real.log (criticalNormalizedReflection n c) := by
        refine Real.log_le_log (by positivity) hbounds.1
      have hlogval : Real.log ((n : ℝ) ^ c / 4) = c * Real.log (n : ℝ) - Real.log 4 := by
        rw [Real.log_div (by positivity) (by norm_num), Real.log_rpow (by linarith)]
      rw [hlogval] at hlog
      rw [le_div_iff₀ hlogpos]
      calc (c - Real.log 4 / Real.log (n : ℝ)) * Real.log (n : ℝ)
          = c * Real.log (n : ℝ) - Real.log 4 := by
            field_simp
        _ ≤ Real.log (criticalNormalizedReflection n c) := hlog
    have hupper : ∀ᶠ n : ℕ in atTop,
        Real.log (criticalNormalizedReflection n c) / Real.log n ≤ c + Real.log 3 / Real.log n := by
      filter_upwards [eventually_gt_atTop 1, hbig] with n hn hn2
      have hnr : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hlogpos : 0 < Real.log (n : ℝ) := Real.log_pos hnr
      have hbounds := criticalNormalizedReflection_bounds hn hc0 hc2 hn2
      have hpc : (0 : ℝ) < (n : ℝ) ^ c := Real.rpow_pos_of_pos (by linarith) c
      have hpos : 0 < criticalNormalizedReflection n c := by
        have := hbounds.1
        have h4 : (0 : ℝ) < (n : ℝ) ^ c / 4 := by positivity
        linarith
      have hlog : Real.log (criticalNormalizedReflection n c) ≤ Real.log (3 * (n : ℝ) ^ c) :=
        Real.log_le_log hpos hbounds.2
      have hlogval : Real.log (3 * (n : ℝ) ^ c) = Real.log 3 + c * Real.log (n : ℝ) := by
        rw [Real.log_mul (by norm_num) (by positivity), Real.log_rpow (by linarith)]
      rw [hlogval] at hlog
      rw [div_le_iff₀ hlogpos]
      calc Real.log (criticalNormalizedReflection n c)
          ≤ Real.log 3 + c * Real.log (n : ℝ) := hlog
        _ = (c + Real.log 3 / Real.log (n : ℝ)) * Real.log (n : ℝ) := by
            field_simp
            ring
    have hlogtop : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have hL : Tendsto (fun n : ℕ => c - Real.log 4 / Real.log n) atTop (𝓝 c) := by
      have h0 : Tendsto (fun n : ℕ => Real.log 4 / Real.log (n : ℝ)) atTop (𝓝 0) :=
        Tendsto.div_atTop tendsto_const_nhds hlogtop
      simpa using tendsto_const_nhds.sub h0
    have hU : Tendsto (fun n : ℕ => c + Real.log 3 / Real.log n) atTop (𝓝 c) := by
      have h0 : Tendsto (fun n : ℕ => Real.log 3 / Real.log (n : ℝ)) atTop (𝓝 0) :=
        Tendsto.div_atTop tendsto_const_nhds hlogtop
      simpa using tendsto_const_nhds.add h0
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hL hU hlower hupper

/-- **Weighted Cesàro transfer over the primes.**  If the ratio of two nonnegative prime weights
converges and the total weight diverges, the weighted averages converge to the same limit. -/
theorem tendsto_weighted_prime_average {t w : ℕ → ℝ} (hw : ∀ p, 0 ≤ w p)
    (hdiv : Tendsto (fun N : ℕ => ∑ p ∈ Nat.primesBelow N, w p) atTop atTop) {L : ℝ}
    (hlim : ∀ ε : ℝ, 0 < ε → ∀ᶠ p : ℕ in atTop, |t p - L * w p| ≤ ε * w p) :
    Tendsto (fun N : ℕ => (∑ p ∈ Nat.primesBelow N, t p) / (∑ p ∈ Nat.primesBelow N, w p))
      atTop (𝓝 L) := by
  classical
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨P, hP⟩ := eventually_atTop.mp (hlim (ε / 2) (by linarith))
  set C : ℝ := ∑ p ∈ Nat.primesBelow P, |t p - L * w p| with hC
  have hCnn : 0 ≤ C := Finset.sum_nonneg fun _ _ => abs_nonneg _
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (hdiv.eventually_ge_atTop (2 * C / ε + 1))
  refine ⟨max N₀ P, fun N hN => ?_⟩
  have hNN₀ : N₀ ≤ N := le_trans (le_max_left _ _) hN
  have hNP : P ≤ N := le_trans (le_max_right _ _) hN
  have hWbig : 2 * C / ε + 1 ≤ ∑ p ∈ Nat.primesBelow N, w p := hN₀ N hNN₀
  have hWpos : 0 < ∑ p ∈ Nat.primesBelow N, w p := by
    have h2C : 0 ≤ 2 * C / ε := by positivity
    linarith
  have hsubset : Nat.primesBelow P ⊆ Nat.primesBelow N := by
    intro q hq
    rw [Nat.mem_primesBelow] at hq ⊢
    exact ⟨lt_of_lt_of_le hq.1 hNP, hq.2⟩
  have hsplit : ∑ p ∈ Nat.primesBelow N, |t p - L * w p|
      = ∑ p ∈ Nat.primesBelow P, |t p - L * w p|
        + ∑ p ∈ (Nat.primesBelow N) \ (Nat.primesBelow P), |t p - L * w p| := by
    rw [← Finset.sum_sdiff hsubset]
    ring
  have htail : ∑ p ∈ (Nat.primesBelow N) \ (Nat.primesBelow P), |t p - L * w p|
      ≤ ∑ p ∈ (Nat.primesBelow N) \ (Nat.primesBelow P), (ε / 2) * w p := by
    refine Finset.sum_le_sum fun q hq => ?_
    rw [Finset.mem_sdiff, Nat.mem_primesBelow, Nat.mem_primesBelow] at hq
    have hqP : P ≤ q := by
      by_contra hcon
      exact hq.2 ⟨by omega, hq.1.2⟩
    exact hP q hqP
  have htail2 : ∑ p ∈ (Nat.primesBelow N) \ (Nat.primesBelow P), (ε / 2) * w p
      ≤ (ε / 2) * ∑ p ∈ Nat.primesBelow N, w p := by
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (by linarith)
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.sdiff_subset) ?_
    intro q _ _
    exact hw q
  have hkey : |∑ p ∈ Nat.primesBelow N, t p - L * ∑ p ∈ Nat.primesBelow N, w p|
      ≤ C + (ε / 2) * ∑ p ∈ Nat.primesBelow N, w p := by
    have hrw : (∑ p ∈ Nat.primesBelow N, t p) - L * ∑ p ∈ Nat.primesBelow N, w p
        = ∑ p ∈ Nat.primesBelow N, (t p - L * w p) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    rw [hrw]
    calc |∑ p ∈ Nat.primesBelow N, (t p - L * w p)|
        ≤ ∑ p ∈ Nat.primesBelow N, |t p - L * w p| := Finset.abs_sum_le_sum_abs _ _
      _ = C + ∑ p ∈ (Nat.primesBelow N) \ (Nat.primesBelow P), |t p - L * w p| := hsplit
      _ ≤ C + (ε / 2) * ∑ p ∈ Nat.primesBelow N, w p := by linarith [htail, htail2]
  have hfrac : (∑ p ∈ Nat.primesBelow N, t p) / (∑ p ∈ Nat.primesBelow N, w p) - L
      = ((∑ p ∈ Nat.primesBelow N, t p) - L * ∑ p ∈ Nat.primesBelow N, w p)
        / (∑ p ∈ Nat.primesBelow N, w p) := by
    field_simp
  rw [Real.dist_eq, hfrac, abs_div, abs_of_pos hWpos, div_lt_iff₀ hWpos]
  have hCsmall : C < (ε / 2) * ∑ p ∈ Nat.primesBelow N, w p := by
    rcases eq_or_lt_of_le hCnn with hC0 | hC0
    · have : (0 : ℝ) < (ε / 2) * ∑ p ∈ Nat.primesBelow N, w p := by positivity
      linarith
    · have hεC : 2 * C / ε < ∑ p ∈ Nat.primesBelow N, w p := by linarith
      rw [div_lt_iff₀ hε] at hεC
      linarith
  calc |∑ p ∈ Nat.primesBelow N, t p - L * ∑ p ∈ Nat.primesBelow N, w p|
      ≤ C + (ε / 2) * ∑ p ∈ Nat.primesBelow N, w p := hkey
    _ < ε * ∑ p ∈ Nat.primesBelow N, w p := by linarith

theorem tendsto_sum_primesBelow_log_atTop :
    Tendsto (fun N : ℕ => ∑ p ∈ Nat.primesBelow N, Real.log (p : ℝ)) atTop atTop := by
  have hratio := tendsto_sum_primesBelow_log_div
  have hhalf : ∀ᶠ N : ℕ in atTop,
      (N : ℝ) / 2 ≤ ∑ p ∈ Nat.primesBelow N, Real.log (p : ℝ) := by
    obtain ⟨M, hM⟩ := Metric.tendsto_atTop.mp hratio (1 / 2) (by norm_num)
    filter_upwards [eventually_ge_atTop M, eventually_gt_atTop 0] with N hN hN0
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN0
    have hdist := hM N hN
    rw [Real.dist_eq, abs_lt] at hdist
    have hge : (1 : ℝ) / 2 < (∑ p ∈ Nat.primesBelow N, Real.log (p : ℝ)) / (N : ℝ) := by
      linarith [hdist.1]
    rw [lt_div_iff₀ hNpos] at hge
    linarith
  refine tendsto_atTop_mono' atTop hhalf ?_
  have hcast : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  exact hcast.atTop_div_const (by norm_num)

/-- **Cofinal exponential type of the critically normalized reflection product.**  The weighted
Cesàro average of the logarithmic types over the primes is the radial drift itself. -/
theorem tendsto_log_prod_criticalNormalizedReflection {c : ℝ} (hc0 : 0 ≤ c) (hc2 : 2 * c ≤ 1) :
    Tendsto (fun N : ℕ =>
        (∑ p ∈ Nat.primesBelow N, Real.log (criticalNormalizedReflection p c))
          / (∑ p ∈ Nat.primesBelow N, Real.log (p : ℝ))) atTop (𝓝 c) := by
  refine tendsto_weighted_prime_average (fun p => Real.log_natCast_nonneg p)
    tendsto_sum_primesBelow_log_atTop ?_
  intro ε hε
  have htype := tendsto_log_criticalNormalizedReflection_div_log hc0 hc2
  have hclose : ∀ᶠ n : ℕ in atTop,
      |Real.log (criticalNormalizedReflection n c) / Real.log (n : ℝ) - c| ≤ ε := by
    have := Metric.tendsto_atTop.mp htype ε hε
    obtain ⟨M, hM⟩ := this
    filter_upwards [eventually_ge_atTop M] with n hn
    have := hM n hn
    rw [Real.dist_eq] at this
    exact this.le
  filter_upwards [hclose, eventually_gt_atTop 1] with n hn hn1
  have hnr : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hlogpos : 0 < Real.log (n : ℝ) := Real.log_pos hnr
  have hrw : Real.log (criticalNormalizedReflection n c) - c * Real.log (n : ℝ)
      = (Real.log (criticalNormalizedReflection n c) / Real.log (n : ℝ) - c)
        * Real.log (n : ℝ) := by
    field_simp
  rw [hrw, abs_mul, abs_of_pos hlogpos]
  exact mul_le_mul_of_nonneg_right hn hlogpos.le

/-- **Superessential cofinal rate.**  Relative to the cutoff itself, the logarithm of the
critically normalized line comparison grows like `|c| N`: the prime number theorem turns the
Cesàro type into a linear rate. -/
theorem tendsto_log_prod_criticalNormalizedReflection_div_natCast {c : ℝ} (hc0 : 0 ≤ c)
    (hc2 : 2 * c ≤ 1) :
    Tendsto (fun N : ℕ =>
        (∑ p ∈ Nat.primesBelow N, Real.log (criticalNormalizedReflection p c)) / (N : ℝ))
      atTop (𝓝 c) := by
  have hA := tendsto_log_prod_criticalNormalizedReflection hc0 hc2
  have hB := tendsto_sum_primesBelow_log_div
  have hprod := hA.mul hB
  rw [mul_one] at hprod
  refine hprod.congr' ?_
  filter_upwards [eventually_gt_atTop 2] with N hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have : 0 < N := by omega
    exact_mod_cast this
  have hsumpos : 0 < ∑ p ∈ Nat.primesBelow N, Real.log (p : ℝ) := by
    have h2 : (2 : ℕ) ∈ Nat.primesBelow N := by
      rw [Nat.mem_primesBelow]
      exact ⟨by omega, Nat.prime_two⟩
    have hpos : 0 < Real.log ((2 : ℕ) : ℝ) := by
      have : (1 : ℝ) < ((2 : ℕ) : ℝ) := by norm_num
      exact Real.log_pos this
    refine Finset.sum_pos' (fun p _ => Real.log_natCast_nonneg p) ⟨2, h2, hpos⟩
  field_simp

end

end RHTower
