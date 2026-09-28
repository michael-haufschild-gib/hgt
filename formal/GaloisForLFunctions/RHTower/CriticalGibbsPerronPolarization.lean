import GaloisForLFunctions.RHTower.MertensSecondTheorem
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
# The pole direction is the Perron vector of the von Mangoldt correspondence

On the divisor lattice `[1, N]` of `ℕ`, the von Mangoldt correspondence is the multiplicative
Toeplitz form `c ↦ 2 Σ_{n ≥ 2} Λ(n) n^{-1/2} Re Σ_m c(nm) conj c(m)`.  The critical Gibbs
vector `m^{-1/2}` (the vector representing the pole functional `f ↦ f̂(i/2)` of the Weil form
on lattice tests, and the critical Bost–Connes Gibbs weight) is its asymptotic top eigenvector:

* `tendsto_gibbs_rayleigh`: its Rayleigh quotient is `log N − γ + o(1)`.  The energy
  `P(N) = Σ_{nm ≤ N} Λ(n)/(nm)` equals `Σ_{k ≤ N} log k / k` (from `Σ_{d ∣ k} Λ(d) = log k`) and
  `Σ_{m ≤ N} S(⌊N/m⌋)/m` (Mertens sums), so `2P − (log N − γ)H` is a `1/m`-average of Mertens
  remainders, which is `o(H(N))` by Mertens' theorem with Euler's constant.
* `exists_vonMangoldt_toeplitz_le`: unconditionally every vector has Rayleigh quotient
  `≤ log N + C` (Schur test with the weight `m^{-1/2}`, whose row sums are
  `log k + S(⌊N/k⌋)`).
* `gibbs_perron_polarization`: both statements in the Toeplitz form.

Euler's constant is the defect of the Perron eigenvalue.
-/

open Filter Topology ArithmeticFunction
open ComplexConjugate

namespace RHTower

noncomputable section

namespace CriticalGibbs

/-- Mertens' partial sum `S(x) = Σ_{n ≤ x} Λ(n)/n`. -/
def mertensPartial (x : ℕ) : ℝ := ∑ n ∈ Finset.Icc 1 x, (vonMangoldt n : ℝ) / n

/-- The harmonic sum `H(N) = Σ_{m ≤ N} 1/m`. -/
def harm (N : ℕ) : ℝ := ∑ m ∈ Finset.Icc 1 N, (1 : ℝ) / m

/-- **Divisor reindexing.**  Pairs `(n, m)` with `n m ≤ N` are the pairs (divisor, multiple). -/
theorem sum_mulPairs_eq_sum_divisors (N : ℕ) (f : ℕ → ℕ → ℝ) :
    ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N, (if n * m ≤ N then f n (n * m) else 0) =
      ∑ k ∈ Finset.Icc 1 N, ∑ n ∈ k.divisors, f n k := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun p : (_ : ℕ) × ℕ => p.1 * p.2 ≤ N)]
  have hzero : ∑ x ∈ (Finset.sigma (Finset.Icc 1 N) fun _ => Finset.Icc 1 N).filter
      (fun p : (_ : ℕ) × ℕ => ¬ p.1 * p.2 ≤ N),
      (if x.1 * x.2 ≤ N then f x.1 (x.1 * x.2) else 0) = 0 :=
    Finset.sum_eq_zero fun x hx => by
      rw [if_neg (Finset.mem_filter.mp hx).2]
  rw [hzero, add_zero]
  refine Finset.sum_bij' (fun p _ => ⟨p.1 * p.2, p.1⟩) (fun q _ => ⟨q.2, q.1 / q.2⟩)
    ?_ ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_sigma, Finset.mem_Icc] at hp
    simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors]
    refine ⟨⟨by nlinarith, hp.2⟩, dvd_mul_right _ _, by nlinarith⟩
  · intro q hq
    simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors] at hq
    obtain ⟨⟨hk1, hkN⟩, hdvd, hk0⟩ := hq
    simp only [Finset.mem_filter, Finset.mem_sigma, Finset.mem_Icc]
    have hn1 : 1 ≤ q.2 := Nat.pos_of_dvd_of_pos hdvd (by omega)
    have hnk : q.2 ≤ q.1 := Nat.le_of_dvd (by omega) hdvd
    have hmul : q.2 * (q.1 / q.2) = q.1 := Nat.mul_div_cancel' hdvd
    have hq1 : 1 ≤ q.1 / q.2 := Nat.div_pos hnk (by omega)
    have hq2 : q.1 / q.2 ≤ N := (Nat.div_le_self _ _).trans hkN
    exact ⟨⟨⟨hn1, hnk.trans hkN⟩, hq1, hq2⟩, by rw [hmul]; exact hkN⟩
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_sigma, Finset.mem_Icc] at hp
    have hp1 : 0 < p.1 := by omega
    ext
    · rfl
    · simp [Nat.mul_div_cancel_left _ hp1]
  · intro q hq
    simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors] at hq
    obtain ⟨_, hdvd, _⟩ := hq
    ext
    · simp [Nat.mul_div_cancel' hdvd]
    · rfl
  · intro p hp
    simp only [Finset.mem_filter] at hp
    rw [if_pos hp.2]

/-- The energy of the critical Gibbs vector `m^{-1/2}` under the von Mangoldt correspondence:
`P(N) = Σ_{n m ≤ N} Λ(n)/(n m)`. -/
def gibbsEnergy (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N,
    (if n * m ≤ N then (vonMangoldt n : ℝ) / ((n : ℝ) * m) else 0)

/-- **Height form.**  `P(N) = Σ_{k ≤ N} log k / k`: the von Mangoldt correspondence integrates
to the height, by `Σ_{d ∣ k} Λ(d) = log k`. -/
theorem gibbsEnergy_eq_height (N : ℕ) :
    gibbsEnergy N = ∑ k ∈ Finset.Icc 1 N, Real.log k / k := by
  have h := sum_mulPairs_eq_sum_divisors N (fun n k => (vonMangoldt n : ℝ) / k)
  have e : gibbsEnergy N = ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N,
      (if n * m ≤ N then (vonMangoldt n : ℝ) / (((n * m : ℕ)) : ℝ) else 0) := by
    unfold gibbsEnergy
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
    push_cast; rfl
  refine e.trans (h.trans ?_)
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_div, ArithmeticFunction.vonMangoldt_sum]

/-- **Mertens form.**  `P(N) = Σ_{m ≤ N} S(⌊N/m⌋)/m`. -/
theorem gibbsEnergy_eq_mertens (N : ℕ) :
    gibbsEnergy N = ∑ m ∈ Finset.Icc 1 N, (1 / (m : ℝ)) * mertensPartial (N / m) := by
  unfold gibbsEnergy mertensPartial
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
  rw [Finset.mul_sum, ← Finset.sum_filter]
  have hset : (Finset.Icc 1 N).filter (fun n => n * m ≤ N) = Finset.Icc 1 (N / m) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨h1, _⟩, h2⟩
      exact ⟨h1, (Nat.le_div_iff_mul_le (by omega)).mpr h2⟩
    · rintro ⟨h1, h2⟩
      have h3 := (Nat.le_div_iff_mul_le (by omega)).mp h2
      exact ⟨⟨h1, le_trans (Nat.le_mul_of_pos_right n (by omega)) h3⟩, h3⟩
  rw [hset]
  refine Finset.sum_congr rfl fun n _ => ?_
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  field_simp

theorem harm_pos {N : ℕ} (hN : 1 ≤ N) : 0 < harm N := by
  unfold harm
  exact Finset.sum_pos (fun m hm => by
    have := (Finset.mem_Icc.mp hm).1
    have : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    positivity) ⟨1, by simp; omega⟩

/-- `log(N+1) ≤ H(N)`. -/
theorem log_succ_le_harm (N : ℕ) : Real.log ((N : ℝ) + 1) ≤ harm N := by
  induction N with
  | zero => simp [harm]
  | succ N ih =>
    unfold harm at ih ⊢
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have h1 : Real.log (((N + 1 : ℕ) : ℝ) + 1) - Real.log ((N : ℝ) + 1) ≤ 1 / ((N + 1 : ℕ) : ℝ) := by
      push_cast
      rw [← Real.log_div (by positivity) hpos.ne']
      have := Real.log_le_sub_one_of_pos (show 0 < ((N : ℝ) + 1 + 1) / ((N : ℝ) + 1) by positivity)
      have e : ((N : ℝ) + 1 + 1) / ((N : ℝ) + 1) - 1 = 1 / ((N : ℝ) + 1) := by
        field_simp; ring
      linarith
    linarith

/-- `1/(N+1) ≤ log(N+1) − log N` for `N ≥ 1`. -/
theorem one_div_succ_le_log_succ_sub {N : ℕ} (hN : 1 ≤ N) :
    1 / ((N : ℝ) + 1) ≤ Real.log ((N : ℝ) + 1) - Real.log N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have h := Real.log_le_sub_one_of_pos (show 0 < (N : ℝ) / ((N : ℝ) + 1) by positivity)
  rw [Real.log_div hN0.ne' (by positivity)] at h
  have e : (N : ℝ) / ((N : ℝ) + 1) - 1 = -(1 / ((N : ℝ) + 1)) := by field_simp; ring
  linarith

/-- The tail `Σ_{M < m ≤ N} 1/m ≤ log N − log M` for `1 ≤ M ≤ N`. -/
theorem sum_Ioc_inv_le_log {M N : ℕ} (hM : 1 ≤ M) (hMN : M ≤ N) :
    ∑ m ∈ Finset.Ioc M N, (1 : ℝ) / m ≤ Real.log N - Real.log M := by
  induction N, hMN using Nat.le_induction with
  | base => simp
  | succ N hMN ih =>
    rw [Finset.sum_Ioc_succ_top (by omega)]
    have h1 := one_div_succ_le_log_succ_sub (show 1 ≤ N by omega)
    push_cast
    linarith

/-- **Cesàro lemma on the divisor lattice.**  If `φ ≥ 0` is bounded and `φ(k) → 0`, then the
`1/m`-average of `φ(⌊N/m⌋)` over `m ≤ N` is `o(H(N))`. -/
theorem tendsto_cesaro_harm {φ : ℕ → ℝ} (hφ0 : ∀ k, 0 ≤ φ k) {B : ℝ} (hB : ∀ k, φ k ≤ B)
    (hφ : Tendsto φ atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (∑ m ∈ Finset.Icc 1 N, (1 / (m : ℝ)) * φ (N / m)) / harm N)
      atTop (𝓝 0) := by
  have hB0 : 0 ≤ B := (hφ0 0).trans (hB 0)
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨K₀, hK₀⟩ := (Metric.tendsto_atTop.mp hφ) (ε / 2) (by linarith)
  set K := max K₀ 1 with hK
  have hK1 : 1 ≤ K := le_max_right _ _
  have hKφ : ∀ k, K ≤ k → φ k ≤ ε / 2 := fun k hk => by
    have := hK₀ k ((le_max_left _ _).trans hk)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hφ0 k)] at this; linarith
  set L : ℝ := B * Real.log (2 * K) with hL
  have hL0 : 0 ≤ L := mul_nonneg hB0 (Real.log_nonneg (by
    have : (1 : ℝ) ≤ K := by exact_mod_cast hK1
    linarith))
  -- choose `N₀` so that `L / log(N+1) < ε/2`
  obtain ⟨N₁, hN₁⟩ : ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N → L / Real.log ((N : ℝ) + 1) < ε / 2 := by
    have ht : Tendsto (fun N : ℕ => L / Real.log ((N : ℝ) + 1)) atTop (𝓝 0) := by
      apply Tendsto.div_atTop tendsto_const_nhds
      exact Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    obtain ⟨N₁, hN₁⟩ := (Metric.tendsto_atTop.mp ht) (ε / 2) (by linarith)
    exact ⟨N₁, fun N hN => by
      have := hN₁ N hN
      rw [Real.dist_eq, sub_zero] at this
      exact lt_of_le_of_lt (le_abs_self _) this⟩
  refine ⟨max (max N₁ K) 1, fun N hN => ?_⟩
  have hNK : K ≤ N := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hN)
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNN₁ : N₁ ≤ N := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hN)
  have hH := harm_pos hN1
  have hlogH := log_succ_le_harm N
  have hlogpos : 0 < Real.log ((N : ℝ) + 1) := Real.log_pos (by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    linarith)
  set F : ℕ → ℝ := fun m => (1 / (m : ℝ)) * φ (N / m) with hF
  have hFnn : ∀ m, 0 ≤ F m := fun m => mul_nonneg (by positivity) (hφ0 _)
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 N) (fun m => K ≤ N / m)]
  have hhead : ∑ m ∈ (Finset.Icc 1 N).filter (fun m => K ≤ N / m), F m ≤ ε / 2 * harm N := by
    calc ∑ m ∈ (Finset.Icc 1 N).filter (fun m => K ≤ N / m), F m
        ≤ ∑ m ∈ (Finset.Icc 1 N).filter (fun m => K ≤ N / m), ε / 2 * (1 / (m : ℝ)) := by
          refine Finset.sum_le_sum fun m hm => ?_
          have := hKφ _ (Finset.mem_filter.mp hm).2
          simp only [hF]
          rw [mul_comm (ε / 2)]
          exact mul_le_mul_of_nonneg_left this (by positivity)
      _ ≤ ∑ m ∈ Finset.Icc 1 N, ε / 2 * (1 / (m : ℝ)) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun m _ _ => by positivity
      _ = ε / 2 * harm N := by rw [← Finset.mul_sum]; rfl
  have htail : ∑ m ∈ (Finset.Icc 1 N).filter (fun m => ¬ K ≤ N / m), F m ≤ L := by
    have hM1 : 1 ≤ N / K := (Nat.one_le_div_iff (by omega)).mpr hNK
    have hsub : (Finset.Icc 1 N).filter (fun m => ¬ K ≤ N / m) ⊆ Finset.Ioc (N / K) N := by
      intro m hm
      simp only [Finset.mem_filter, Finset.mem_Icc, not_le] at hm
      simp only [Finset.mem_Ioc]
      refine ⟨?_, hm.1.2⟩
      have h1 : N < K * m := by
        have := (Nat.div_lt_iff_lt_mul (by omega)).mp hm.2
        linarith [mul_comm m K]
      exact (Nat.div_lt_iff_lt_mul (by omega)).mpr (by linarith [mul_comm K m])
    calc ∑ m ∈ (Finset.Icc 1 N).filter (fun m => ¬ K ≤ N / m), F m
        ≤ ∑ m ∈ (Finset.Icc 1 N).filter (fun m => ¬ K ≤ N / m), B * (1 / (m : ℝ)) :=
          Finset.sum_le_sum fun m _ => by
            simp only [hF]; rw [mul_comm B]
            exact mul_le_mul_of_nonneg_left (hB _) (by positivity)
      _ ≤ ∑ m ∈ Finset.Ioc (N / K) N, B * (1 / (m : ℝ)) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun m _ _ => by positivity
      _ = B * ∑ m ∈ Finset.Ioc (N / K) N, (1 : ℝ) / m := by rw [Finset.mul_sum]
      _ ≤ B * (Real.log N - Real.log ((N / K : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left (sum_Ioc_inv_le_log hM1 (Nat.div_le_self _ _)) hB0
      _ ≤ L := by
          apply mul_le_mul_of_nonneg_left _ hB0
          have hMpos : (0 : ℝ) < ((N / K : ℕ) : ℝ) := by exact_mod_cast (show 0 < N / K by omega)
          rw [← Real.log_div (by positivity) hMpos.ne']
          apply Real.log_le_log (by positivity)
          rw [div_le_iff₀ hMpos]
          have hlt : N < K * (N / K + 1) := by
            have := Nat.lt_div_mul_add (a := N) (b := K) (by omega)
            linarith [mul_comm (N / K) K, Nat.mul_succ K (N / K)]
          have hcast : (N : ℝ) < K * ((N / K : ℕ) + 1 : ℝ) := by exact_mod_cast hlt
          have h2 : ((N / K : ℕ) : ℝ) + 1 ≤ 2 * ((N / K : ℕ) : ℝ) := by
            have : (1 : ℝ) ≤ ((N / K : ℕ) : ℝ) := by exact_mod_cast hM1
            linarith
          have hK0 : (0 : ℝ) ≤ K := by positivity
          nlinarith
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg
    (add_nonneg (Finset.sum_nonneg fun m _ => hFnn m) (Finset.sum_nonneg fun m _ => hFnn m))
    hH.le)]
  rw [div_lt_iff₀ hH]
  have hq := hN₁ N hNN₁
  have hLH : L < ε / 2 * harm N := by
    have h1 : L < ε / 2 * Real.log ((N : ℝ) + 1) := by
      have := (div_lt_iff₀ hlogpos).mp hq; linarith
    have h2 : ε / 2 * Real.log ((N : ℝ) + 1) ≤ ε / 2 * harm N :=
      mul_le_mul_of_nonneg_left hlogH (by linarith)
    linarith
  have : ε / 2 * harm N + ε / 2 * harm N = ε * harm N := by ring
  nlinarith

/-- The floor defect: `|log m + log ⌊N/m⌋ − log N| ≤ 1/⌊N/m⌋` for `1 ≤ m ≤ N`. -/
theorem abs_log_floor_defect_le {N m : ℕ} (hm : 1 ≤ m) (hmN : m ≤ N) :
    |Real.log m + Real.log ((N / m : ℕ) : ℝ) - Real.log N| ≤ 1 / ((N / m : ℕ) : ℝ) := by
  set k := N / m with hk
  have hk1 : 1 ≤ k := (Nat.one_le_div_iff (by omega)).mpr hmN
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hle : k * m ≤ N := Nat.div_mul_le_self N m
  have hlt : N < k * m + m := Nat.lt_div_mul_add (by omega)
  have hleR : (k : ℝ) * m ≤ N := by exact_mod_cast hle
  have hltR : (N : ℝ) < (k + 1) * m := by
    have : (N : ℝ) < (k : ℝ) * m + m := by exact_mod_cast hlt
    linarith
  have hN0 : (0 : ℝ) < N := by linarith [mul_pos hk0 hm0]
  have hupper : Real.log m + Real.log k - Real.log N ≤ 0 := by
    rw [← Real.log_mul hm0.ne' hk0.ne']
    have := Real.log_le_log (by positivity) (show (m : ℝ) * k ≤ N by linarith)
    linarith
  have hlower : -(1 / (k : ℝ)) ≤ Real.log m + Real.log k - Real.log N := by
    have h1 : Real.log N ≤ Real.log m + Real.log ((k : ℝ) + 1) := by
      rw [← Real.log_mul hm0.ne' (by positivity)]
      exact Real.log_le_log hN0 (by linarith)
    have h2 : Real.log ((k : ℝ) + 1) - Real.log k ≤ 1 / (k : ℝ) := by
      rw [← Real.log_div (by positivity) hk0.ne']
      have := Real.log_le_sub_one_of_pos (show 0 < ((k : ℝ) + 1) / k by positivity)
      have e : ((k : ℝ) + 1) / k - 1 = 1 / (k : ℝ) := by field_simp; ring
      linarith
    linarith
  rw [abs_le]; constructor <;> linarith

/-- **The critical Gibbs vector is the asymptotic Perron vector of the von Mangoldt
correspondence.**  Its Rayleigh quotient `2 P(N)/H(N)`, with `P(N) = Σ_{nm ≤ N} Λ(n)/(nm)` the
energy of `m^{-1/2}` and `H(N) = Σ_{m ≤ N} 1/m` its mass, is `log N − γ + o(1)`. -/
theorem tendsto_gibbs_rayleigh :
    Tendsto (fun N : ℕ => 2 * gibbsEnergy N / harm N -
      (Real.log N - Real.eulerMascheroniConstant)) atTop (𝓝 0) := by
  set γ := Real.eulerMascheroniConstant
  set E : ℕ → ℝ := fun k => mertensPartial k - Real.log k + γ with hEdef
  have hE : Tendsto E atTop (𝓝 0) := by
    have h := tendsto_sum_vonMangoldt_div_sub_log.add_const γ
    rw [neg_add_cancel] at h
    exact h
  set φ : ℕ → ℝ := fun k => |E k| + 1 / (k : ℝ) with hφdef
  have hφ : Tendsto φ atTop (𝓝 0) := by
    have h1 : Tendsto (fun k => |E k|) atTop (𝓝 0) := by
      have := (continuous_abs.tendsto (0 : ℝ)).comp hE
      rw [abs_zero] at this
      exact this
    have := h1.add tendsto_one_div_atTop_nhds_zero_nat
    rw [add_zero] at this
    exact this
  have hφ0 : ∀ k, 0 ≤ φ k := fun k => add_nonneg (abs_nonneg _) (by positivity)
  obtain ⟨B, hB⟩ := hφ.bddAbove_range
  have hBk : ∀ k, φ k ≤ B := fun k => hB ⟨k, rfl⟩
  have hces := tendsto_cesaro_harm hφ0 hBk hφ
  refine squeeze_zero_norm' ?_ hces
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN
  have hH := harm_pos hN
  have hid : 2 * gibbsEnergy N - (Real.log N - γ) * harm N =
      ∑ m ∈ Finset.Icc 1 N, (1 / (m : ℝ)) *
        (Real.log m + mertensPartial (N / m) - Real.log N + γ) := by
    have h2 : 2 * gibbsEnergy N = (∑ k ∈ Finset.Icc 1 N, Real.log k / k) +
        ∑ m ∈ Finset.Icc 1 N, (1 / (m : ℝ)) * mertensPartial (N / m) := by
      rw [two_mul]; nth_rewrite 1 [gibbsEnergy_eq_height]; rw [gibbsEnergy_eq_mertens]
    rw [h2, harm, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    ring
  rw [Real.norm_eq_abs, show 2 * gibbsEnergy N / harm N - (Real.log N - γ) =
      (2 * gibbsEnergy N - (Real.log N - γ) * harm N) / harm N by field_simp,
    abs_div, abs_of_pos hH, hid]
  apply div_le_div_of_nonneg_right _ hH.le
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun m hm => ?_)
  obtain ⟨hm1, hmN⟩ := Finset.mem_Icc.mp hm
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / m)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hfl := abs_log_floor_defect_le hm1 hmN
  have e : Real.log m + mertensPartial (N / m) - Real.log N + γ =
      E (N / m) + (Real.log m + Real.log ((N / m : ℕ) : ℝ) - Real.log N) := by
    simp only [hEdef]; ring
  rw [e]
  exact (abs_add_le _ _).trans (by simp only [hφdef]; linarith)

/-- **Schur ceiling (the Perron eigenvalue is `log N + O(1)`).**  Unconditionally, for every `c`
supported in `[1, N]`, the von Mangoldt correspondence form is at most `(log N + C) Σ|c|²`:
the Schur test with the critical Gibbs weight `m^{-1/2}` has row sums
`Σ_{d ∣ k} Λ(d) + Σ_{n ≤ N/k} Λ(n)/n = log k + S(⌊N/k⌋) ≤ log N + C`. -/
theorem exists_vonMangoldt_toeplitz_le :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N → ∀ c : ℕ → ℂ, (∀ m, N < m → c m = 0) →
      2 * ∑ n ∈ Finset.Icc 2 N, (vonMangoldt n : ℝ) / Real.sqrt n *
          (∑ m ∈ Finset.Icc 1 N, c (n * m) * conj (c m)).re ≤
        (Real.log N + C) * ∑ m ∈ Finset.Icc 1 N, ‖c m‖ ^ 2 := by
  set γ := Real.eulerMascheroniConstant
  set E : ℕ → ℝ := fun k => mertensPartial k - Real.log k + γ with hEdef
  have hE : Tendsto E atTop (𝓝 0) := by
    have h := tendsto_sum_vonMangoldt_div_sub_log.add_const γ
    rw [neg_add_cancel] at h
    exact h
  obtain ⟨B, hB⟩ := hE.bddAbove_range
  refine ⟨B - γ, fun N hN c hc => ?_⟩
  -- AM–GM with the weight ratio `√n`
  have hpair : ∀ n ∈ Finset.Icc 2 N, ∀ m ∈ Finset.Icc 1 N,
      (vonMangoldt n : ℝ) / Real.sqrt n * 2 * (c (n * m) * conj (c m)).re ≤
        (if n * m ≤ N then (vonMangoldt n : ℝ) * ‖c (n * m)‖ ^ 2 +
          (vonMangoldt n : ℝ) / n * ‖c m‖ ^ 2 else 0) := by
    intro n hn m hm
    have hn2 := (Finset.mem_Icc.mp hn).1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
    have hΛ : (0 : ℝ) ≤ vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
    split_ifs with hnm
    · have hre : (c (n * m) * conj (c m)).re ≤ ‖c (n * m)‖ * ‖c m‖ := by
        refine (Complex.re_le_norm _).trans (le_of_eq ?_)
        rw [norm_mul, Complex.norm_conj]
      have hsq : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn0.le
      have hamgm : 2 * (‖c (n * m)‖ * ‖c m‖) ≤
          Real.sqrt n * ‖c (n * m)‖ ^ 2 + ‖c m‖ ^ 2 / Real.sqrt n := by
        have h := sq_nonneg (Real.sqrt n * ‖c (n * m)‖ - ‖c m‖)
        have : Real.sqrt n * ‖c (n * m)‖ ^ 2 + ‖c m‖ ^ 2 / Real.sqrt n -
            2 * (‖c (n * m)‖ * ‖c m‖) =
            (Real.sqrt n * ‖c (n * m)‖ - ‖c m‖) ^ 2 / Real.sqrt n := by
          field_simp; ring
        have : 0 ≤ (Real.sqrt n * ‖c (n * m)‖ - ‖c m‖) ^ 2 / Real.sqrt n := by positivity
        linarith
      calc (vonMangoldt n : ℝ) / Real.sqrt n * 2 * (c (n * m) * conj (c m)).re
          ≤ (vonMangoldt n : ℝ) / Real.sqrt n * (2 * (‖c (n * m)‖ * ‖c m‖)) := by
            rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ ≤ (vonMangoldt n : ℝ) / Real.sqrt n *
            (Real.sqrt n * ‖c (n * m)‖ ^ 2 + ‖c m‖ ^ 2 / Real.sqrt n) :=
            mul_le_mul_of_nonneg_left hamgm (by positivity)
        _ = (vonMangoldt n : ℝ) * ‖c (n * m)‖ ^ 2 + (vonMangoldt n : ℝ) / n * ‖c m‖ ^ 2 := by
            have key : (vonMangoldt n : ℝ) / Real.sqrt n *
                (Real.sqrt n * ‖c (n * m)‖ ^ 2 + ‖c m‖ ^ 2 / Real.sqrt n) =
                (vonMangoldt n : ℝ) * ‖c (n * m)‖ ^ 2 +
                  (vonMangoldt n : ℝ) / (Real.sqrt n * Real.sqrt n) * ‖c m‖ ^ 2 := by
              field_simp
            rw [key, hsq]
    · have hz : c (n * m) = 0 := hc _ (by omega)
      simp [hz]
  -- sum the pairwise bounds
  have hsum : 2 * ∑ n ∈ Finset.Icc 2 N, (vonMangoldt n : ℝ) / Real.sqrt n *
      (∑ m ∈ Finset.Icc 1 N, c (n * m) * conj (c m)).re ≤
      ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N,
        (if n * m ≤ N then (vonMangoldt n : ℝ) * ‖c (n * m)‖ ^ 2 +
          (vonMangoldt n : ℝ) / n * ‖c m‖ ^ 2 else 0) := by
    rw [Finset.mul_sum]
    have hsub : Finset.Icc 2 N ⊆ Finset.Icc 1 N := Finset.Icc_subset_Icc_left (by norm_num)
    calc ∑ n ∈ Finset.Icc 2 N, 2 * ((vonMangoldt n : ℝ) / Real.sqrt n *
            (∑ m ∈ Finset.Icc 1 N, c (n * m) * conj (c m)).re)
        ≤ ∑ n ∈ Finset.Icc 2 N, ∑ m ∈ Finset.Icc 1 N,
            (if n * m ≤ N then (vonMangoldt n : ℝ) * ‖c (n * m)‖ ^ 2 +
              (vonMangoldt n : ℝ) / n * ‖c m‖ ^ 2 else 0) := by
          refine Finset.sum_le_sum fun n hn => ?_
          rw [Complex.re_sum, Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_le_sum fun m hm => ?_
          have := hpair n hn m hm
          linarith
      _ ≤ ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N,
            (if n * m ≤ N then (vonMangoldt n : ℝ) * ‖c (n * m)‖ ^ 2 +
              (vonMangoldt n : ℝ) / n * ‖c m‖ ^ 2 else 0) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => ?_
          refine Finset.sum_nonneg fun m _ => ?_
          split_ifs
          · have hΛ : (0 : ℝ) ≤ vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
            positivity
          · rfl
  -- the two halves: divisor sums and Mertens sums
  have hA := sum_mulPairs_eq_sum_divisors N (fun n k => (vonMangoldt n : ℝ) * ‖c k‖ ^ 2)
  have hsplit : ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N,
      (if n * m ≤ N then (vonMangoldt n : ℝ) * ‖c (n * m)‖ ^ 2 +
        (vonMangoldt n : ℝ) / n * ‖c m‖ ^ 2 else 0) =
      (∑ k ∈ Finset.Icc 1 N, Real.log k * ‖c k‖ ^ 2) +
        ∑ m ∈ Finset.Icc 1 N, mertensPartial (N / m) * ‖c m‖ ^ 2 := by
    have e1 : ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N,
        (if n * m ≤ N then (vonMangoldt n : ℝ) * ‖c (n * m)‖ ^ 2 +
          (vonMangoldt n : ℝ) / n * ‖c m‖ ^ 2 else 0) =
        (∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N,
          (if n * m ≤ N then (vonMangoldt n : ℝ) * ‖c (n * m)‖ ^ 2 else 0)) +
        ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N,
          (if n * m ≤ N then (vonMangoldt n : ℝ) / n * ‖c m‖ ^ 2 else 0) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun m _ => ?_
      split_ifs <;> simp
    rw [e1, hA]
    congr 1
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [← Finset.sum_mul, ArithmeticFunction.vonMangoldt_sum]
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun m hm => ?_
      have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
      rw [← Finset.sum_filter]
      have hset : (Finset.Icc 1 N).filter (fun n => n * m ≤ N) = Finset.Icc 1 (N / m) := by
        ext n
        simp only [Finset.mem_filter, Finset.mem_Icc]
        constructor
        · rintro ⟨⟨h1, _⟩, h2⟩
          exact ⟨h1, (Nat.le_div_iff_mul_le (by omega)).mpr h2⟩
        · rintro ⟨h1, h2⟩
          have h3 := (Nat.le_div_iff_mul_le (by omega)).mp h2
          exact ⟨⟨h1, le_trans (Nat.le_mul_of_pos_right n (by omega)) h3⟩, h3⟩
      rw [hset, ← Finset.sum_mul]
      rfl
  -- row-sum bound `log k + S(⌊N/k⌋) ≤ log N + B − γ`
  have hrow : ∀ k ∈ Finset.Icc 1 N, Real.log k + mertensPartial (N / k) ≤ Real.log N + (B - γ) := by
    intro k hk
    obtain ⟨hk1, hkN⟩ := Finset.mem_Icc.mp hk
    have hEk := hB ⟨N / k, rfl⟩
    have hfl := abs_log_floor_defect_le hk1 hkN
    have hup : Real.log k + Real.log ((N / k : ℕ) : ℝ) - Real.log N ≤ 0 := by
      have := (abs_le.mp hfl).2
      have hpos : (0 : ℝ) ≤ 1 / ((N / k : ℕ) : ℝ) := by positivity
      -- from the proof: the defect is nonpositive
      set q := N / k
      have hq1 : 1 ≤ q := (Nat.one_le_div_iff (by omega)).mpr hkN
      have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
      have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
      rw [← Real.log_mul hk0.ne' hq0.ne']
      have hle : q * k ≤ N := Nat.div_mul_le_self N k
      have hleR : (k : ℝ) * q ≤ N := by
        have : ((q * k : ℕ) : ℝ) ≤ N := by exact_mod_cast hle
        push_cast at this; linarith
      have := Real.log_le_log (by positivity) hleR
      linarith
    simp only [hEdef] at hEk
    linarith
  calc 2 * ∑ n ∈ Finset.Icc 2 N, (vonMangoldt n : ℝ) / Real.sqrt n *
          (∑ m ∈ Finset.Icc 1 N, c (n * m) * conj (c m)).re
      ≤ (∑ k ∈ Finset.Icc 1 N, Real.log k * ‖c k‖ ^ 2) +
          ∑ m ∈ Finset.Icc 1 N, mertensPartial (N / m) * ‖c m‖ ^ 2 := hsum.trans (le_of_eq hsplit)
    _ = ∑ k ∈ Finset.Icc 1 N, (Real.log k + mertensPartial (N / k)) * ‖c k‖ ^ 2 := by
        rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun k _ => ?_; ring
    _ ≤ ∑ k ∈ Finset.Icc 1 N, (Real.log N + (B - γ)) * ‖c k‖ ^ 2 :=
        Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_right (hrow k hk) (sq_nonneg _)
    _ = (Real.log N + (B - γ)) * ∑ m ∈ Finset.Icc 1 N, ‖c m‖ ^ 2 := by rw [Finset.mul_sum]

/-- The critical Gibbs vector `m ↦ m^{-1/2}` on `[1, N]`. -/
def gibbsVec (N : ℕ) (m : ℕ) : ℂ := if m ≤ N then ((1 / Real.sqrt m : ℝ) : ℂ) else 0

theorem gibbsVec_toeplitz (N : ℕ) :
    2 * ∑ n ∈ Finset.Icc 2 N, (vonMangoldt n : ℝ) / Real.sqrt n *
        (∑ m ∈ Finset.Icc 1 N, gibbsVec N (n * m) * conj (gibbsVec N m)).re =
      2 * gibbsEnergy N := by
  congr 1
  have hsplit : gibbsEnergy N = ∑ n ∈ Finset.Icc 2 N, ∑ m ∈ Finset.Icc 1 N,
      (if n * m ≤ N then (vonMangoldt n : ℝ) / ((n : ℝ) * m) else 0) := by
    unfold gibbsEnergy
    symm
    refine Finset.sum_subset (Finset.Icc_subset_Icc_left (by norm_num)) fun n hn hnot => ?_
    have hn1 : n = 1 := by
      simp only [Finset.mem_Icc, not_and_or, not_le] at hn hnot
      omega
    subst hn1
    simp [ArithmeticFunction.vonMangoldt_apply_one]
  rw [hsplit]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn0 : (0 : ℝ) < n := by
    have := (Finset.mem_Icc.mp hn).1; exact_mod_cast (show 0 < n by omega)
  rw [Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  obtain ⟨hm1, hmN⟩ := Finset.mem_Icc.mp hm
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  by_cases hnm : n * m ≤ N
  · simp only [gibbsVec, if_pos hmN, Complex.conj_ofReal, ← Complex.ofReal_mul,
      Complex.ofReal_re, if_pos hnm]
    have hsq : Real.sqrt ((n * m : ℕ) : ℝ) = Real.sqrt n * Real.sqrt m := by
      push_cast; exact Real.sqrt_mul hn0.le _
    rw [hsq]
    have hsn : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn0.le
    have hsm : Real.sqrt m * Real.sqrt m = m := Real.mul_self_sqrt hm0.le
    have hsn0 : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
    have hsm0 : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm0
    calc (vonMangoldt n : ℝ) / Real.sqrt n *
          (1 / (Real.sqrt n * Real.sqrt m) * (1 / Real.sqrt m))
        = (vonMangoldt n : ℝ) / ((Real.sqrt n * Real.sqrt n) * (Real.sqrt m * Real.sqrt m)) := by
          field_simp
      _ = (vonMangoldt n : ℝ) / ((n : ℝ) * m) := by rw [hsn, hsm]
  · simp [gibbsVec, if_neg hnm]

theorem gibbsVec_mass (N : ℕ) : ∑ m ∈ Finset.Icc 1 N, ‖gibbsVec N m‖ ^ 2 = harm N := by
  unfold harm
  refine Finset.sum_congr rfl fun m hm => ?_
  obtain ⟨hm1, hmN⟩ := Finset.mem_Icc.mp hm
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  simp only [gibbsVec, if_pos hmN, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_pos (by positivity), div_pow, one_pow, Real.sq_sqrt hm0.le]

/-- **Perron–polarization theorem.**  For the von Mangoldt correspondence on the divisor lattice
`[1, N]`, the critical Gibbs vector `m^{-1/2}` (the pole direction of the Weil form) has Rayleigh
quotient `log N − γ + o(1)`, while every vector has Rayleigh quotient at most `log N + C`: it is
the asymptotic top eigenvector, and Euler's constant is the defect of its eigenvalue. -/
theorem gibbs_perron_polarization :
    Tendsto (fun N : ℕ => (2 * ∑ n ∈ Finset.Icc 2 N, (vonMangoldt n : ℝ) / Real.sqrt n *
        (∑ m ∈ Finset.Icc 1 N, gibbsVec N (n * m) * conj (gibbsVec N m)).re) /
        (∑ m ∈ Finset.Icc 1 N, ‖gibbsVec N m‖ ^ 2) -
        (Real.log N - Real.eulerMascheroniConstant)) atTop (𝓝 0) ∧
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N → ∀ c : ℕ → ℂ, (∀ m, N < m → c m = 0) →
      2 * ∑ n ∈ Finset.Icc 2 N, (vonMangoldt n : ℝ) / Real.sqrt n *
          (∑ m ∈ Finset.Icc 1 N, c (n * m) * conj (c m)).re ≤
        (Real.log N + C) * ∑ m ∈ Finset.Icc 1 N, ‖c m‖ ^ 2 := by
  refine ⟨?_, exists_vonMangoldt_toeplitz_le⟩
  simp only [gibbsVec_toeplitz, gibbsVec_mass]
  exact tendsto_gibbs_rayleigh

end CriticalGibbs

end

end RHTower
