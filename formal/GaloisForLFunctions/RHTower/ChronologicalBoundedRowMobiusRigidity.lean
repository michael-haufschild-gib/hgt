import GaloisForLFunctions.RHTower.ChronologicalHarmonicCharge
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# Bounded chronological rows are forced to the Möbius function

For a row `a` of length `N` the heat residual `r(t) = e^{-t} + Σ_{k ≤ N} a_k β(kt)`,
`β(t) = 1/t − 1/(e^t − 1)`, has the Lambert expansion, for `t > 0` and every `n ≥ 1`,

  `r(t) = c/t + Σ_{m ≤ n} ρ_m e^{-mt} − Σ_{k ≤ N} a_k R_{n,k}(t)`,
  `ρ_m = [m = 1] − Σ_{k ≤ N, k ∣ m} a_k`,

where `c = Σ a_k/k` is the harmonic charge and `R_{n,k}(t) = x^{⌊n/k⌋+1}/(1 − x)`, `x = e^{-kt}`, is
the part of `1/(e^{kt} − 1)` beyond order `n`. For `|a_k| ≤ C` and `t ≥ 1` the tail is at most
`2C(n+3)e^{-(n+1)t}`. Averaging over `[T, T+1]` gives the residue bound
(`abs_chronologicalLambertResidue_le`)

  `|ρ_n| ≤ e^{n(T+1)}(‖r‖ + |c| + Σ_{m<n} |ρ_m|) + 2C(n+3)e^{-T}`.

Consequences, for rows bounded by a fixed `C` whose residuals tend to `0` in `L²(0,∞)`:

* every residue tends to `0` (`tendsto_chronologicalLambertResidue_zero`);
* every coefficient tends to `μ(n)` (`tendsto_chronologicalRow_moebius`);
* a fixed node set carrying such rows contains every `n` with `μ(n) ≠ 0`
  (`mem_of_moebius_ne_zero_of_tendsto`);
* bounded rows on a node set missing such an `n`, for instance the primes, keep a positive
  residual (`exists_chronologicalL2Norm_floor_of_not_mem`, `exists_chronologicalL2Norm_floor_primes`).

Integer dilates of the Bose defect are complete with unbounded coefficients, even along the
primes alone. With bounded coefficients the support of every successful row family must exhaust
the squarefree integers.
-/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ArithmeticFunction.Moebius
namespace RHTower
open GaloisForLFunctions.HTGeometry.ChronologicalTensor

/-- The coefficient of `e^{-mt}` in the Lambert expansion of a finite heat residual. -/
def chronologicalLambertResidue (a : ℕ → ℝ) (N m : ℕ) : ℝ :=
  (if m = 1 then 1 else 0) - ∑ k ∈ (Finset.Ioc 0 N).filter (· ∣ m), a k

/-- The part of `1/(e^{kt} − 1)` beyond the Lambert terms of order at most `n`. -/
def chronologicalLambertTail (n k : ℕ) (t : ℝ) : ℝ :=
  1 / (Real.exp ((k:ℝ) * t) - 1) -
    ∑ m ∈ (Finset.Icc 1 n).filter (k ∣ ·), Real.exp (-((m:ℝ) * t))

/-- The Lambert terms of order at most `n` attached to `k` are a finite geometric sum. -/
theorem sum_filter_dvd_exp_eq_geom {n k : ℕ} (hk : 0 < k) (t : ℝ) :
    (∑ m ∈ (Finset.Icc 1 n).filter (k ∣ ·), Real.exp (-((m:ℝ) * t))) =
      ∑ i ∈ Finset.range (n / k), Real.exp (-((k:ℝ) * t)) ^ (i + 1) := by
  apply Finset.sum_nbij' (fun m => m / k - 1) (fun i => k * (i + 1))
  · intro m hm
    simp only [Finset.mem_filter, Finset.mem_Icc] at hm
    obtain ⟨⟨h1, hn⟩, q, rfl⟩ := hm
    have hq : 0 < q := by
      rcases Nat.eq_zero_or_pos q with h | h
      · simp [h] at h1
      · exact h
    simp only [Finset.mem_range]
    rw [Nat.mul_div_cancel_left q hk]
    have : q ≤ n / k := (Nat.le_div_iff_mul_le hk).mpr (by linarith [mul_comm k q])
    omega
  · intro i hi
    simp only [Finset.mem_range] at hi
    simp only [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨?_, ?_⟩, dvd_mul_right _ _⟩
    · exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hk.ne' (Nat.succ_ne_zero i))
    · calc k * (i + 1) ≤ k * (n / k) := Nat.mul_le_mul_left _ hi
        _ ≤ n := Nat.mul_div_le n k
  · intro m hm
    simp only [Finset.mem_filter, Finset.mem_Icc] at hm
    obtain ⟨⟨h1, _⟩, q, rfl⟩ := hm
    have hq : 0 < q := by
      rcases Nat.eq_zero_or_pos q with h | h
      · simp [h] at h1
      · exact h
    rw [Nat.mul_div_cancel_left q hk]
    congr 1
    omega
  · intro i _
    rw [Nat.mul_div_cancel_left _ hk]
    omega
  · intro m hm
    simp only [Finset.mem_filter, Finset.mem_Icc] at hm
    obtain ⟨⟨h1, _⟩, q, rfl⟩ := hm
    have hq : 0 < q := by
      rcases Nat.eq_zero_or_pos q with h | h
      · simp [h] at h1
      · exact h
    rw [Nat.mul_div_cancel_left q hk, Nat.sub_add_cancel hq, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring

/-- Exact form of the Lambert tail: `x^{⌊n/k⌋+1}/(1 − x)` with `x = e^{-kt}`. -/
theorem chronologicalLambertTail_eq {n k : ℕ} (hk : 0 < k) {t : ℝ} (ht : 0 < t) :
    chronologicalLambertTail n k t =
      Real.exp (-((k:ℝ) * t)) ^ (n / k + 1) / (1 - Real.exp (-((k:ℝ) * t))) := by
  set x := Real.exp (-((k:ℝ) * t)) with hx
  have hk' : (0:ℝ) < k := by exact_mod_cast hk
  have hx1 : x < 1 := by
    rw [hx, ← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by nlinarith)
  have hx0 : 0 < x := Real.exp_pos _
  have hden : (1:ℝ) - x ≠ 0 := by linarith
  have he : Real.exp ((k:ℝ) * t) = x⁻¹ := by rw [hx, Real.exp_neg, inv_inv]
  have hxne : x - 1 ≠ 0 := by linarith
  unfold chronologicalLambertTail
  rw [sum_filter_dvd_exp_eq_geom hk t, ← hx]
  have hgeom : (∑ i ∈ Finset.range (n / k), x ^ (i + 1)) = x * ((x ^ (n / k) - 1) / (x - 1)) := by
    rw [← geom_sum_eq (by linarith : x ≠ 1), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hgeom, he]
  have hinv : (1:ℝ) / (x⁻¹ - 1) = x / (1 - x) := by
    field_simp
  rw [hinv]
  field_simp
  ring

/-- The Lambert tail is nonnegative and, for `kt ≥ 1`, at most `2e^{-k(⌊n/k⌋+1)t}`. -/
theorem chronologicalLambertTail_nonneg_le {n k : ℕ} (hk : 0 < k) {t : ℝ} (ht : 1 ≤ t) :
    0 ≤ chronologicalLambertTail n k t ∧
      chronologicalLambertTail n k t ≤ 2 * Real.exp (-(((n+1 + (k - (n+1)) : ℕ):ℝ) * t)) := by
  have ht0 : 0 < t := by linarith
  have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hk
  set x := Real.exp (-((k:ℝ) * t)) with hx
  have hx0 : 0 < x := Real.exp_pos _
  have hxh : x ≤ 1/2 := by
    have hkt : 1 ≤ (k:ℝ) * t := by nlinarith
    rw [hx, Real.exp_neg]
    have h2 : 2 ≤ Real.exp ((k:ℝ) * t) := by linarith [Real.add_one_le_exp ((k:ℝ) * t)]
    rw [one_div]
    exact inv_anti₀ (by norm_num) h2
  rw [chronologicalLambertTail_eq hk ht0, ← hx]
  have hden : 0 < 1 - x := by linarith
  refine ⟨div_nonneg (pow_nonneg hx0.le _) hden.le, ?_⟩
  have hfrac : x ^ (n / k + 1) / (1 - x) ≤ 2 * x ^ (n / k + 1) := by
    rw [div_le_iff₀ hden]
    have := pow_nonneg hx0.le (n / k + 1)
    nlinarith
  refine hfrac.trans ?_
  have hexp : x ^ (n / k + 1) = Real.exp (-(((k * (n / k + 1) : ℕ):ℝ) * t)) := by
    rw [hx, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [hexp]
  have hle : n + 1 + (k - (n+1)) ≤ k * (n / k + 1) := by
    have h1 : n < k * (n / k + 1) := Nat.lt_mul_div_succ n hk
    have h2 : k ≤ k * (n / k + 1) := Nat.le_mul_of_pos_right k (Nat.succ_pos _)
    omega
  have hle' : (((n+1 + (k - (n+1)) : ℕ):ℝ)) * t ≤ ((k * (n / k + 1) : ℕ):ℝ) * t :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hle) ht0.le
  have := Real.exp_le_exp.mpr (neg_le_neg hle')
  linarith

/-- `Σ_{k ≤ N} q^{k ∸ m} ≤ m + 2` for `0 ≤ q ≤ 1/2`. -/
theorem sum_Ioc_pow_tsub_le {q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 1/2) (N m : ℕ) :
    (∑ k ∈ Finset.Ioc 0 N, q ^ (k - m)) ≤ m + 2 := by
  have hsub : Finset.Ioc 0 N ⊆ Finset.range (N + 1) := by
    intro k hk
    simp only [Finset.mem_Ioc] at hk
    simp only [Finset.mem_range]
    omega
  have h1 : (∑ k ∈ Finset.Ioc 0 N, q ^ (k - m)) ≤ ∑ k ∈ Finset.range (N + 1), q ^ (k - m) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => pow_nonneg hq0 _)
  refine h1.trans ?_
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (N + 1)) (· < m)]
  have hA : (∑ k ∈ (Finset.range (N + 1)).filter (· < m), q ^ (k - m)) ≤ m := by
    have hsubm : (Finset.range (N + 1)).filter (· < m) ⊆ Finset.range m := by
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢
      exact hk.2
    calc (∑ k ∈ (Finset.range (N + 1)).filter (· < m), q ^ (k - m))
        ≤ ∑ _k ∈ (Finset.range (N + 1)).filter (· < m), (1:ℝ) :=
          Finset.sum_le_sum (fun k _ => pow_le_one₀ hq0 (by linarith))
      _ = ((Finset.range (N + 1)).filter (· < m)).card := by simp
      _ ≤ (Finset.range m).card := by exact_mod_cast Finset.card_le_card hsubm
      _ = m := by simp
  have hB : (∑ k ∈ (Finset.range (N + 1)).filter (fun k => ¬ k < m), q ^ (k - m)) ≤ 2 := by
    have himg : (∑ k ∈ (Finset.range (N + 1)).filter (fun k => ¬ k < m), q ^ (k - m)) =
        ∑ i ∈ ((Finset.range (N + 1)).filter (fun k => ¬ k < m)).image (fun k => k - m), q ^ i := by
      rw [Finset.sum_image]
      intro k₁ hk₁ k₂ hk₂ he
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hk₁ hk₂
      simp only at he
      omega
    rw [himg]
    have hsub2 : ((Finset.range (N + 1)).filter (fun k => ¬ k < m)).image (fun k => k - m) ⊆
        Finset.range (N + 1) := by
      intro i hi
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range] at hi ⊢
      obtain ⟨k, ⟨hk, _⟩, rfl⟩ := hi
      omega
    calc (∑ i ∈ ((Finset.range (N + 1)).filter (fun k => ¬ k < m)).image (fun k => k - m), q ^ i)
        ≤ ∑ i ∈ Finset.range (N + 1), q ^ i :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub2 (fun _ _ _ => pow_nonneg hq0 _)
      _ = (1 - q ^ (N + 1)) / (1 - q) := by
          rw [geom_sum_eq (by linarith : q ≠ 1), show (1:ℝ) - q ^ (N + 1) = -(q ^ (N + 1) - 1) by ring,
            show (1:ℝ) - q = -(q - 1) by ring, neg_div_neg_eq]
      _ ≤ 2 := by
          have hq1 : 0 < 1 - q := by linarith
          rw [div_le_iff₀ hq1]
          have := pow_nonneg hq0 (N + 1)
          nlinarith
  linarith

/-- Lambert expansion of a finite heat residual up to order `n`, with the exact tail. -/
theorem chronologicalHeatError_lambert_expansion (a : ℕ → ℝ) (N : ℕ) {n : ℕ} (hn : 1 ≤ n)
    {t : ℝ} (ht : 0 < t) :
    chronologicalHeatError a N t = chronologicalHarmonicCharge a N / t +
      ∑ m ∈ Finset.Icc 1 n, chronologicalLambertResidue a N m * Real.exp (-((m:ℝ) * t)) -
      ∑ k ∈ Finset.Ioc 0 N, a k * chronologicalLambertTail n k t := by
  rw [chronologicalHeatError_charge_decomposition a N ht]
  have hsplit : chronologicalBoseSum a N t =
      (∑ k ∈ Finset.Ioc 0 N, ∑ m ∈ (Finset.Icc 1 n).filter (k ∣ ·),
        a k * Real.exp (-((m:ℝ) * t))) +
      ∑ k ∈ Finset.Ioc 0 N, a k * chronologicalLambertTail n k t := by
    unfold chronologicalBoseSum
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [← Finset.mul_sum, ← mul_add]
    unfold chronologicalLambertTail
    ring
  have hswap : (∑ k ∈ Finset.Ioc 0 N, ∑ m ∈ (Finset.Icc 1 n).filter (k ∣ ·),
        a k * Real.exp (-((m:ℝ) * t))) =
      ∑ m ∈ Finset.Icc 1 n, ∑ k ∈ (Finset.Ioc 0 N).filter (· ∣ m),
        a k * Real.exp (-((m:ℝ) * t)) := by
    apply Finset.sum_comm'
    intro k m
    simp only [Finset.mem_filter]
    tauto
  have hexp : Real.exp (-t) =
      ∑ m ∈ Finset.Icc 1 n, (if m = 1 then (1:ℝ) else 0) * Real.exp (-((m:ℝ) * t)) := by
    have h1 : (1:ℕ) ∈ Finset.Icc 1 n := Finset.mem_Icc.mpr ⟨le_rfl, hn⟩
    simp only [ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq' (Finset.Icc 1 n) 1, if_pos h1]
    simp
  rw [hsplit, hswap, hexp]
  unfold chronologicalLambertResidue
  simp only [sub_mul, Finset.sum_sub_distrib, Finset.sum_mul]
  ring

/-- The Lambert tails of a row bounded by `C` are at most `2C(n+3)e^{-(n+1)t}` for `t ≥ 1`. -/
theorem abs_sum_mul_chronologicalLambertTail_le (a : ℕ → ℝ) (N : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ k ∈ Finset.Ioc 0 N, |a k| ≤ C) (n : ℕ) {t : ℝ} (ht : 1 ≤ t) :
    |∑ k ∈ Finset.Ioc 0 N, a k * chronologicalLambertTail n k t| ≤
      2 * C * ((n:ℝ) + 3) * Real.exp (-(((n:ℝ) + 1) * t)) := by
  have ht0 : 0 < t := by linarith
  set q := Real.exp (-t) with hq
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hqh : q ≤ 1/2 := by
    rw [hq, Real.exp_neg, one_div]
    exact inv_anti₀ (by norm_num) (by linarith [Real.add_one_le_exp t])
  have hterm (k : ℕ) (hk : k ∈ Finset.Ioc 0 N) :
      |a k * chronologicalLambertTail n k t| ≤
        2 * C * Real.exp (-(((n:ℝ) + 1) * t)) * q ^ (k - (n+1)) := by
    have hk0 : 0 < k := (Finset.mem_Ioc.mp hk).1
    obtain ⟨h0, hle⟩ := chronologicalLambertTail_nonneg_le (n := n) hk0 ht
    have hexp : Real.exp (-(((n+1 + (k - (n+1)) : ℕ):ℝ) * t)) =
        Real.exp (-(((n:ℝ) + 1) * t)) * q ^ (k - (n+1)) := by
      rw [hq, ← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      push_cast
      ring
    rw [abs_mul, abs_of_nonneg h0]
    calc |a k| * chronologicalLambertTail n k t
        ≤ C * (2 * Real.exp (-(((n+1 + (k - (n+1)) : ℕ):ℝ) * t))) :=
          mul_le_mul (ha k hk) hle h0 hC
      _ = _ := by rw [hexp]; ring
  calc |∑ k ∈ Finset.Ioc 0 N, a k * chronologicalLambertTail n k t|
      ≤ ∑ k ∈ Finset.Ioc 0 N, |a k * chronologicalLambertTail n k t| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.Ioc 0 N, 2 * C * Real.exp (-(((n:ℝ) + 1) * t)) * q ^ (k - (n+1)) :=
        Finset.sum_le_sum hterm
    _ = 2 * C * Real.exp (-(((n:ℝ) + 1) * t)) * ∑ k ∈ Finset.Ioc 0 N, q ^ (k - (n+1)) := by
        rw [Finset.mul_sum]
    _ ≤ 2 * C * Real.exp (-(((n:ℝ) + 1) * t)) * (((n + 1 : ℕ) : ℝ) + 2) :=
        mul_le_mul_of_nonneg_left (sum_Ioc_pow_tsub_le hq0 hqh N (n+1)) (by positivity)
    _ = _ := by push_cast; ring

/-- Pointwise residue bound at a time `t ≥ 1`. -/
theorem abs_chronologicalLambertResidue_le_pointwise (a : ℕ → ℝ) (N : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ k ∈ Finset.Ioc 0 N, |a k| ≤ C) {n : ℕ} (hn : 1 ≤ n) {t : ℝ} (ht : 1 ≤ t) :
    |chronologicalLambertResidue a N n| ≤
      Real.exp ((n:ℝ) * t) * (|chronologicalHeatError a N t| + |chronologicalHarmonicCharge a N| +
        ∑ m ∈ Finset.Icc 1 (n - 1), |chronologicalLambertResidue a N m|) +
      2 * C * ((n:ℝ) + 3) * Real.exp (-t) := by
  have ht0 : 0 < t := by linarith
  set ρ := chronologicalLambertResidue a N with hρ
  set c := chronologicalHarmonicCharge a N
  set R := ∑ k ∈ Finset.Ioc 0 N, a k * chronologicalLambertTail n k t with hR
  set S := ∑ m ∈ Finset.Icc 1 (n - 1), ρ m * Real.exp (-((m:ℝ) * t)) with hS
  have hexpand := chronologicalHeatError_lambert_expansion a N hn ht0
  have hn' : n - 1 + 1 = n := Nat.sub_add_cancel hn
  have hsplit : (∑ m ∈ Finset.Icc 1 n, ρ m * Real.exp (-((m:ℝ) * t))) =
      S + ρ n * Real.exp (-((n:ℝ) * t)) := by
    conv_lhs => rw [← hn']
    rw [Finset.sum_Icc_succ_top (by omega), hn']
  rw [hsplit] at hexpand
  have hE : Real.exp ((n:ℝ) * t) * Real.exp (-((n:ℝ) * t)) = 1 := by
    rw [← Real.exp_add]; simp
  have hid : ρ n = Real.exp ((n:ℝ) * t) *
      (chronologicalHeatError a N t - c / t - S + R) := by
    rw [hexpand]
    have : chronologicalHeatError a N t - c / t - S + R = ρ n * Real.exp (-((n:ℝ) * t)) := by
      rw [hexpand]; ring
    rw [← hexpand, this, mul_comm, mul_assoc, mul_comm (Real.exp _), hE, mul_one]
  have hc : |c / t| ≤ |c| := by
    rw [abs_div, abs_of_pos ht0]
    exact div_le_self (abs_nonneg _) ht
  have hSb : |S| ≤ ∑ m ∈ Finset.Icc 1 (n - 1), |ρ m| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun m hm => ?_)
    have hm1 : (1:ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    have : Real.exp (-((m:ℝ) * t)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith
    nlinarith [abs_nonneg (ρ m)]
  have hRb := abs_sum_mul_chronologicalLambertTail_le a N C hC ha n ht
  have hRe : Real.exp ((n:ℝ) * t) * |R| ≤ 2 * C * ((n:ℝ) + 3) * Real.exp (-t) := by
    have hmul : Real.exp ((n:ℝ) * t) * Real.exp (-(((n:ℝ) + 1) * t)) = Real.exp (-t) := by
      rw [← Real.exp_add]; congr 1; ring
    calc Real.exp ((n:ℝ) * t) * |R|
        ≤ Real.exp ((n:ℝ) * t) * (2 * C * ((n:ℝ) + 3) * Real.exp (-(((n:ℝ) + 1) * t))) :=
          mul_le_mul_of_nonneg_left hRb (Real.exp_pos _).le
      _ = 2 * C * ((n:ℝ) + 3) * (Real.exp ((n:ℝ) * t) * Real.exp (-(((n:ℝ) + 1) * t))) := by ring
      _ = _ := by rw [hmul]
  rw [hid, abs_mul, abs_of_pos (Real.exp_pos _)]
  have htri : |chronologicalHeatError a N t - c / t - S + R| ≤
      |chronologicalHeatError a N t| + |c / t| + |S| + |R| := by
    have h1 := abs_add_le (chronologicalHeatError a N t - c / t - S) R
    have h2 := abs_sub (chronologicalHeatError a N t - c / t) S
    have h3 := abs_sub (chronologicalHeatError a N t) (c / t)
    linarith
  have hpos := Real.exp_pos ((n:ℝ) * t)
  calc Real.exp ((n:ℝ) * t) * |chronologicalHeatError a N t - c / t - S + R|
      ≤ Real.exp ((n:ℝ) * t) * (|chronologicalHeatError a N t| + |c / t| + |S| + |R|) :=
        mul_le_mul_of_nonneg_left htri hpos.le
    _ ≤ Real.exp ((n:ℝ) * t) * (|chronologicalHeatError a N t| + |c| +
          ∑ m ∈ Finset.Icc 1 (n - 1), |ρ m|) + Real.exp ((n:ℝ) * t) * |R| := by
        nlinarith
    _ ≤ _ := by linarith

/-- The average of `|f|` over a unit interval in `(0,∞)` is at most the `L²` norm. -/
theorem integral_abs_Ioc_le_chronologicalL2Norm {f : ℝ → ℝ}
    (hf : MemLp f 2 chronologicalPositiveVolume) {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in Ioc T (T+1), |f t|) ≤ chronologicalL2Norm f := by
  have hsub : Ioc T (T+1) ⊆ Ioi 0 := fun t ht => lt_of_le_of_lt hT ht.1
  have hfm : MemLp f 2 (volume.restrict (Ioc T (T+1))) :=
    hf.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hg : MemLp (fun _t : ℝ => (1:ℝ)) 2 (volume.restrict (Ioc T (T+1))) := memLp_const 1
  have hcs := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (by simpa using hfm) (by simpa using hg)
  have hc : (∫ t in Ioc T (T+1), |f t|) ≤ Real.sqrt (∫ t in Ioc T (T+1), f t^2) := by
    rw [Real.sqrt_eq_rpow]
    simpa [Real.norm_eq_abs, Real.rpow_two, sq_abs] using hcs
  have hsq : (∫ t in Ioc T (T+1), f t^2) ≤ ∫ t in Ioi (0:ℝ), f t^2 :=
    integral_mono_measure (Measure.restrict_mono hsub le_rfl)
      (Eventually.of_forall (fun t => sq_nonneg _)) hf.integrable_sq
  rw [chronologicalL2Norm_eq_sqrt hf.1]
  exact hc.trans (Real.sqrt_le_sqrt hsq)

/-- **Residue bound.** For a row bounded by `C`, `n ≥ 1` and `T ≥ 1`,
`|ρ_n| ≤ e^{n(T+1)}(‖r‖ + |c| + Σ_{m<n} |ρ_m|) + 2C(n+3)e^{-T}`. -/
theorem abs_chronologicalLambertResidue_le (a : ℕ → ℝ) (N : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ k ∈ Finset.Ioc 0 N, |a k| ≤ C) {n : ℕ} (hn : 1 ≤ n) {T : ℝ} (hT : 1 ≤ T) :
    |chronologicalLambertResidue a N n| ≤
      Real.exp ((n:ℝ) * (T+1)) * (chronologicalL2Norm (chronologicalHeatError a N) +
        |chronologicalHarmonicCharge a N| +
        ∑ m ∈ Finset.Icc 1 (n - 1), |chronologicalLambertResidue a N m|) +
      2 * C * ((n:ℝ) + 3) * Real.exp (-T) := by
  set r := chronologicalHeatError a N
  set K := |chronologicalHarmonicCharge a N| +
    ∑ m ∈ Finset.Icc 1 (n - 1), |chronologicalLambertResidue a N m| with hK
  have hK0 : 0 ≤ K := by
    rw [hK]; exact add_nonneg (abs_nonneg _) (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  have hT0 : 0 < T := by linarith
  set E := Real.exp ((n:ℝ) * (T+1))
  set B := 2 * C * ((n:ℝ) + 3) * Real.exp (-T)
  have hp (t : ℝ) (ht : t ∈ Ioc T (T+1)) :
      |chronologicalLambertResidue a N n| ≤ E * (|r t| + K) + B := by
    have ht1 : 1 ≤ t := by linarith [ht.1]
    have hpt := abs_chronologicalLambertResidue_le_pointwise a N C hC ha hn ht1
    have he1 : Real.exp ((n:ℝ) * t) ≤ E :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 (Nat.cast_nonneg n))
    have he2 : Real.exp (-t) ≤ Real.exp (-T) := Real.exp_le_exp.mpr (by linarith [ht.1])
    have hb2 : 2 * C * ((n:ℝ) + 3) * Real.exp (-t) ≤ B :=
      mul_le_mul_of_nonneg_left he2 (by positivity)
    have hsum : 0 ≤ |r t| + K := add_nonneg (abs_nonneg _) hK0
    calc |chronologicalLambertResidue a N n|
        ≤ Real.exp ((n:ℝ) * t) * (|r t| + K) + 2 * C * ((n:ℝ) + 3) * Real.exp (-t) := by
          simpa only [hK, add_assoc] using hpt
      _ ≤ E * (|r t| + K) + B := add_le_add (mul_le_mul_of_nonneg_right he1 hsum) hb2
  have hr : IntegrableOn (fun t => |r t|) (Ioc T (T+1)) := by
    have hfm := (chronologicalHeatError_memLp a N).mono_measure
      (Measure.restrict_mono (show Ioc T (T+1) ⊆ Ioi 0 from fun t ht => lt_trans hT0 ht.1) le_rfl)
    exact (hfm.integrable (by simp : (1:ENNReal) ≤ 2)).abs
  have hint : IntegrableOn (fun t => E * (|r t| + K) + B) (Ioc T (T+1)) :=
    ((hr.add (integrableOn_const (hs := measure_Ioc_lt_top.ne))).const_mul E).add
      (integrableOn_const (hs := measure_Ioc_lt_top.ne))
  have hi := setIntegral_mono_on
    (integrableOn_const (C := |chronologicalLambertResidue a N n|) (hs := measure_Ioc_lt_top.ne))
    hint measurableSet_Ioc hp
  have hir : (∫ t in Ioc T (T+1), E * (|r t| + K) + B) =
      E * ((∫ t in Ioc T (T+1), |r t|) + K) + B := by
    have h0 : IntegrableOn (fun t => |r t| + K) (Ioc T (T+1)) :=
      hr.add (integrableOn_const (hs := measure_Ioc_lt_top.ne))
    have h1 : IntegrableOn (fun t => E * (|r t| + K)) (Ioc T (T+1)) := h0.const_mul E
    rw [integral_add h1 (integrableOn_const (hs := measure_Ioc_lt_top.ne)), integral_const_mul,
      integral_add hr (integrableOn_const (hs := measure_Ioc_lt_top.ne))]
    simp
  rw [hir] at hi
  simp at hi
  have hu := integral_abs_Ioc_le_chronologicalL2Norm (chronologicalHeatError_memLp a N) hT0.le
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  calc |chronologicalLambertResidue a N n|
      ≤ E * ((∫ t in Ioc T (T+1), |r t|) + K) + B := hi
    _ ≤ E * (chronologicalL2Norm r + K) + B := by
        have := mul_le_mul_of_nonneg_left (add_le_add hu (le_refl K)) hE0
        linarith
    _ = _ := by rw [hK]; ring

/-- Harmonic charges of bounded rows with vanishing residuals tend to zero (rows of arbitrary
lengths). -/
theorem tendsto_chronologicalHarmonicCharge_zero_of_rows (a : ℕ → ℕ → ℝ) (N : ℕ → ℕ) (C : ℝ)
    (hC : 0 ≤ C) (ha : ∀ j, ∀ k ∈ Finset.Ioc 0 (N j), |a j k| ≤ C)
    (hE : Tendsto (fun j => chronologicalL2Norm (chronologicalHeatError (a j) (N j)))
      atTop (𝓝 0)) :
    Tendsto (fun j => chronologicalHarmonicCharge (a j) (N j)) atTop (𝓝 0) := by
  have hd' : Tendsto (fun T : ℝ => (T*Real.exp (-T)+Real.exp (-T))*(1+4*C))
      atTop (𝓝 0) := by
    simpa only [pow_one, zero_add, zero_mul] using
      ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).add
        Real.tendsto_exp_neg_atTop_nhds_zero).mul_const (1+4*C)
  have hd : Tendsto (fun T : ℝ => (T+1)*(1+4*C)*Real.exp (-T)) atTop (𝓝 0) := by
    convert hd' using 1
    funext T
    ring
  rw [Metric.tendsto_atTop] at hd hE ⊢
  intro η hη
  obtain ⟨T₀,hT₀⟩ := hd (η/2) (by linarith)
  let T := max 1 T₀
  have hT : 1 ≤ T := le_max_left _ _
  have hsmall := hT₀ T (le_max_right _ _)
  rw [Real.dist_eq, sub_zero] at hsmall
  have hs : (T+1)*(1+4*C)*Real.exp (-T) < η/2 :=
    lt_of_le_of_lt (le_abs_self _) hsmall
  obtain ⟨j₀,hj₀⟩ := hE (η/(2*(T+1))) (by positivity)
  refine ⟨j₀, fun j hj => ?_⟩
  have he := hj₀ j hj
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (chronologicalL2Norm_nonneg _)] at he
  have he' := (lt_div_iff₀ (show 0 < 2*(T+1) by positivity)).mp he
  have hb := chronologicalHarmonicCharge_L2_bound (a j) (N j) C hC (ha j) hT
  rw [Real.dist_eq, sub_zero]
  nlinarith

/-- **Every Lambert residue of a successful bounded row family tends to zero.** -/
theorem tendsto_chronologicalLambertResidue_zero (a : ℕ → ℕ → ℝ) (N : ℕ → ℕ) (C : ℝ)
    (hC : 0 ≤ C) (ha : ∀ j, ∀ k ∈ Finset.Ioc 0 (N j), |a j k| ≤ C)
    (hE : Tendsto (fun j => chronologicalL2Norm (chronologicalHeatError (a j) (N j)))
      atTop (𝓝 0)) :
    ∀ n, 1 ≤ n → Tendsto (fun j => chronologicalLambertResidue (a j) (N j) n) atTop (𝓝 0) := by
  have hc := tendsto_chronologicalHarmonicCharge_zero_of_rows a N C hC ha hE
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn
  have hprev : Tendsto (fun j => ∑ m ∈ Finset.Icc 1 (n - 1),
      |chronologicalLambertResidue (a j) (N j) m|) atTop (𝓝 0) := by
    have := tendsto_finsetSum (Finset.Icc 1 (n - 1)) (fun m hm =>
      (ih m (by have := (Finset.mem_Icc.mp hm).2; omega)
        (Finset.mem_Icc.mp hm).1).abs)
    simpa using this
  have hS : Tendsto (fun j => chronologicalL2Norm (chronologicalHeatError (a j) (N j)) +
      |chronologicalHarmonicCharge (a j) (N j)| + ∑ m ∈ Finset.Icc 1 (n - 1),
        |chronologicalLambertResidue (a j) (N j) m|) atTop (𝓝 0) := by
    simpa using (hE.add hc.abs).add hprev
  have htail : Tendsto (fun T : ℝ => 2 * C * ((n:ℝ) + 3) * Real.exp (-T)) atTop (𝓝 0) := by
    simpa using Real.tendsto_exp_neg_atTop_nhds_zero.const_mul (2 * C * ((n:ℝ) + 3))
  rw [Metric.tendsto_atTop] at htail hS ⊢
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := htail (ε/2) (by linarith)
  set T := max 1 T₀
  have hT : 1 ≤ T := le_max_left _ _
  have hBT := hT₀ T (le_max_right _ _)
  rw [Real.dist_eq, sub_zero] at hBT
  have hB : 2 * C * ((n:ℝ) + 3) * Real.exp (-T) < ε/2 := lt_of_le_of_lt (le_abs_self _) hBT
  have hE0 : 0 < Real.exp ((n:ℝ) * (T+1)) := Real.exp_pos _
  obtain ⟨j₀, hj₀⟩ := hS (ε/2 / Real.exp ((n:ℝ) * (T+1))) (by positivity)
  refine ⟨j₀, fun j hj => ?_⟩
  have hsm := hj₀ j hj
  rw [Real.dist_eq, sub_zero] at hsm
  have hsm' : Real.exp ((n:ℝ) * (T+1)) *
      (chronologicalL2Norm (chronologicalHeatError (a j) (N j)) +
        |chronologicalHarmonicCharge (a j) (N j)| + ∑ m ∈ Finset.Icc 1 (n - 1),
          |chronologicalLambertResidue (a j) (N j) m|) < ε/2 := by
    have h := lt_of_le_of_lt (le_abs_self _) hsm
    rw [lt_div_iff₀ hE0] at h
    linarith
  have hbound := abs_chronologicalLambertResidue_le (a j) (N j) C hC (ha j) hn hT
  rw [Real.dist_eq, sub_zero]
  linarith

/-- `Σ_{d ∣ n} μ(d) = [n = 1]` over the reals. -/
theorem sum_divisors_moebius_real (n : ℕ) :
    (∑ d ∈ n.divisors, (μ d : ℝ)) = if n = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => (f n : ℝ))
    ArithmeticFunction.moebius_mul_coe_zeta
  simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
  push_cast at h
  rw [h]

/-- The divisor sum in a residue, written over all divisors of `m`. -/
theorem sum_filter_dvd_eq_sum_divisors (a : ℕ → ℝ) (N : ℕ) {m : ℕ} (hm : 1 ≤ m) :
    (∑ k ∈ (Finset.Ioc 0 N).filter (· ∣ m), a k) =
      ∑ k ∈ m.divisors, if k ≤ N then a k else 0 := by
  rw [← Finset.sum_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext k
  simp only [Finset.mem_filter, Finset.mem_Ioc, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨_, hkN⟩, hkm⟩
    exact ⟨⟨hkm, by omega⟩, hkN⟩
  · rintro ⟨⟨hkm, _⟩, hkN⟩
    exact ⟨⟨Nat.pos_of_dvd_of_pos hkm (by omega), hkN⟩, hkm⟩

/-- **Möbius rigidity.** If rows bounded by a fixed `C` have heat residuals tending to `0` in
`L²(0,∞)`, then every coefficient tends to the Möbius function. -/
theorem tendsto_chronologicalRow_moebius (a : ℕ → ℕ → ℝ) (N : ℕ → ℕ) (C : ℝ)
    (hC : 0 ≤ C) (ha : ∀ j, ∀ k ∈ Finset.Ioc 0 (N j), |a j k| ≤ C)
    (hE : Tendsto (fun j => chronologicalL2Norm (chronologicalHeatError (a j) (N j)))
      atTop (𝓝 0)) :
    ∀ n, 1 ≤ n → Tendsto (fun j => if n ≤ N j then a j n else 0) atTop (𝓝 (μ n : ℝ)) := by
  have hres := tendsto_chronologicalLambertResidue_zero a N C hC ha hE
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn
  have hn0 : n ≠ 0 := by omega
  have hid (j : ℕ) : (if n ≤ N j then a j n else 0) =
      (if n = 1 then (1:ℝ) else 0) - chronologicalLambertResidue (a j) (N j) n -
        ∑ k ∈ n.properDivisors, (if k ≤ N j then a j k else 0) := by
    unfold chronologicalLambertResidue
    rw [sum_filter_dvd_eq_sum_divisors (a j) (N j) hn, ← Nat.insert_self_properDivisors hn0,
      Finset.sum_insert Nat.self_notMem_properDivisors]
    ring
  have hprop : Tendsto (fun j => ∑ k ∈ n.properDivisors, (if k ≤ N j then a j k else 0))
      atTop (𝓝 (∑ k ∈ n.properDivisors, (μ k : ℝ))) := by
    apply tendsto_finsetSum
    intro k hk
    have hk' := Nat.mem_properDivisors.mp hk
    exact ih k hk'.2 (Nat.pos_of_dvd_of_pos hk'.1 (by omega))
  have hlim : Tendsto (fun j => (if n = 1 then (1:ℝ) else 0) -
      chronologicalLambertResidue (a j) (N j) n -
        ∑ k ∈ n.properDivisors, (if k ≤ N j then a j k else 0)) atTop
      (𝓝 ((if n = 1 then (1:ℝ) else 0) - 0 - ∑ k ∈ n.properDivisors, (μ k : ℝ))) :=
    (tendsto_const_nhds.sub (hres n hn)).sub hprop
  have hμ : (if n = 1 then (1:ℝ) else 0) - 0 - ∑ k ∈ n.properDivisors, (μ k : ℝ) = μ n := by
    have hsum := sum_divisors_moebius_real n
    rw [← Nat.insert_self_properDivisors hn0,
      Finset.sum_insert Nat.self_notMem_properDivisors] at hsum
    linarith
  rw [hμ] at hlim
  exact hlim.congr (fun j => (hid j).symm)

/-- **Node-set rigidity.** If bounded rows supported on `S` have heat residuals tending to `0`,
then `S` contains every `n ≥ 1` with `μ(n) ≠ 0`. -/
theorem mem_of_moebius_ne_zero_of_tendsto (S : Set ℕ) (a : ℕ → ℕ → ℝ) (N : ℕ → ℕ) (C : ℝ)
    (hC : 0 ≤ C) (ha : ∀ j, ∀ k ∈ Finset.Ioc 0 (N j), |a j k| ≤ C)
    (hS : ∀ j, ∀ k ∈ Finset.Ioc 0 (N j), k ∉ S → a j k = 0)
    (hE : Tendsto (fun j => chronologicalL2Norm (chronologicalHeatError (a j) (N j)))
      atTop (𝓝 0))
    {n : ℕ} (hn : 1 ≤ n) (hμ : μ n ≠ 0) : n ∈ S := by
  by_contra hnS
  have hlim := tendsto_chronologicalRow_moebius a N C hC ha hE n hn
  have hzero : (fun j => if n ≤ N j then a j n else 0) = fun _ => (0:ℝ) := by
    funext j
    split_ifs with h
    · exact hS j n (Finset.mem_Ioc.mpr ⟨hn, h⟩) hnS
    · rfl
  rw [hzero] at hlim
  have := tendsto_nhds_unique tendsto_const_nhds hlim
  exact hμ (by exact_mod_cast this.symm)

/-- **Positive floor off the Möbius support.** If `S` misses some `n ≥ 1` with `μ(n) ≠ 0`, then
rows supported on `S` with coefficients bounded by `C` keep a heat residual at least some
`ε > 0`. -/
theorem exists_chronologicalL2Norm_floor_of_not_mem (S : Set ℕ) (C : ℝ) (hC : 0 ≤ C)
    {n : ℕ} (hn : 1 ≤ n) (hμ : μ n ≠ 0) (hnS : n ∉ S) :
    ∃ ε > 0, ∀ (b : ℕ → ℝ) (M : ℕ), (∀ k ∈ Finset.Ioc 0 M, |b k| ≤ C) →
      (∀ k ∈ Finset.Ioc 0 M, k ∉ S → b k = 0) →
        ε ≤ chronologicalL2Norm (chronologicalHeatError b M) := by
  by_contra h
  push Not at h
  have hseq (j : ℕ) := h (1 / ((j:ℝ) + 1)) (by positivity)
  choose b M hb hsupp hsmall using hseq
  have hE : Tendsto (fun j => chronologicalL2Norm (chronologicalHeatError (b j) (M j)))
      atTop (𝓝 0) := by
    apply squeeze_zero (fun j => chronologicalL2Norm_nonneg _) (fun j => (hsmall j).le)
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  exact hnS (mem_of_moebius_ne_zero_of_tendsto S b M C hC hb hsupp hE hn hμ)

/-- Bounded rows supported on the primes never approximate `e^{-t}`: the integer dilates
`β(pt)` are complete, but only with unbounded coefficients. -/
theorem exists_chronologicalL2Norm_floor_primes (C : ℝ) (hC : 0 ≤ C) :
    ∃ ε > 0, ∀ (b : ℕ → ℝ) (M : ℕ), (∀ k ∈ Finset.Ioc 0 M, |b k| ≤ C) →
      (∀ k ∈ Finset.Ioc 0 M, ¬ k.Prime → b k = 0) →
        ε ≤ chronologicalL2Norm (chronologicalHeatError b M) :=
  exists_chronologicalL2Norm_floor_of_not_mem {p | p.Prime} C hC le_rfl
    (by simp) (by simpa using Nat.not_prime_one)

/-- Adding the coefficient at `1` does not help: rows supported on `{1} ∪ primes` and bounded
by `C` also keep a positive residual (the obstruction is `μ(6) = 1`). -/
theorem exists_chronologicalL2Norm_floor_one_primes (C : ℝ) (hC : 0 ≤ C) :
    ∃ ε > 0, ∀ (b : ℕ → ℝ) (M : ℕ), (∀ k ∈ Finset.Ioc 0 M, |b k| ≤ C) →
      (∀ k ∈ Finset.Ioc 0 M, k ≠ 1 → ¬ k.Prime → b k = 0) →
        ε ≤ chronologicalL2Norm (chronologicalHeatError b M) := by
  have hμ6 : μ 6 = 1 := by
    have hcop : Nat.Coprime 2 3 := by norm_num
    rw [show (6:ℕ) = 2 * 3 by norm_num,
      ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,
      ArithmeticFunction.moebius_apply_prime Nat.prime_two,
      ArithmeticFunction.moebius_apply_prime Nat.prime_three]
    norm_num
  obtain ⟨ε, hε, hfloor⟩ := exists_chronologicalL2Norm_floor_of_not_mem
    {k | k = 1 ∨ k.Prime} C hC (n := 6) (by norm_num) (by rw [hμ6]; norm_num)
    (by
      simp only [Set.mem_setOf_eq, not_or]
      exact ⟨by norm_num, by decide⟩)
  refine ⟨ε, hε, fun b M hb hsupp => hfloor b M hb (fun k hk hkS => ?_)⟩
  simp only [Set.mem_setOf_eq, not_or] at hkS
  exact hsupp k hk hkS.1 hkS.2

/-- **No `ℓ^p` producers.** For every exponent `p ≥ 1` and every bound `C`, rows with
`Σ_k |a_k|^p ≤ C` never have heat residuals tending to zero: they would be bounded, hence
pointwise Möbius, and `Σ_{n ∈ S} |μ(n)|^p = |S|` on any finite set `S` of primes. The criterion
of MUST-831 therefore lives at `p = ∞` only. -/
theorem not_tendsto_of_sum_pow_le (a : ℕ → ℕ → ℝ) (N : ℕ → ℕ) {p : ℕ} (hp : 1 ≤ p) (C : ℝ)
    (ha : ∀ j, ∑ k ∈ Finset.Ioc 0 (N j), |a j k| ^ p ≤ C) :
    ¬ Tendsto (fun j => chronologicalL2Norm (chronologicalHeatError (a j) (N j)))
      atTop (𝓝 0) := by
  intro hE
  have hC0 : 0 ≤ C := (Finset.sum_nonneg fun _ _ => pow_nonneg (abs_nonneg _) _).trans (ha 0)
  have hbd : ∀ j, ∀ k ∈ Finset.Ioc 0 (N j), |a j k| ≤ max 1 C := by
    intro j k hk
    have hterm : |a j k| ^ p ≤ C :=
      (Finset.single_le_sum (fun i _ => pow_nonneg (abs_nonneg (a j i)) p) hk).trans (ha j)
    by_cases h1 : |a j k| ≤ 1
    · exact h1.trans (le_max_left _ _)
    · push Not at h1
      have : |a j k| ≤ |a j k| ^ p := by
        calc |a j k| = |a j k| ^ 1 := (pow_one _).symm
          _ ≤ |a j k| ^ p := pow_le_pow_right₀ h1.le hp
      exact (this.trans hterm).trans (le_max_right _ _)
  have hlim := tendsto_chronologicalRow_moebius a N (max 1 C) (by positivity) hbd hE
  obtain ⟨S, hSprime, hScard⟩ : ∃ S : Finset ℕ, (∀ n ∈ S, n.Prime) ∧ C < S.card := by
    obtain ⟨m, hm⟩ := exists_nat_gt C
    refine ⟨(Finset.range m).image (Nat.nth Nat.Prime), ?_, ?_⟩
    · intro n hn
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hn
      exact Nat.prime_nth_prime i
    · rw [Finset.card_image_of_injective _ (Nat.nth_injective Nat.infinite_setOf_prime),
        Finset.card_range]
      exact hm
  have hsum : Tendsto (fun j => ∑ n ∈ S, |(if n ≤ N j then a j n else 0)| ^ p) atTop
      (𝓝 (∑ n ∈ S, |(μ n : ℝ)| ^ p)) :=
    tendsto_finsetSum S fun n hn =>
      ((hlim n (hSprime n hn).one_lt.le).abs).pow p
  have hval : (∑ n ∈ S, |(μ n : ℝ)| ^ p) = S.card := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [ArithmeticFunction.moebius_apply_prime (hSprime n hn)]
    simp
  rw [hval] at hsum
  have hle : ∀ j, (∑ n ∈ S, |(if n ≤ N j then a j n else 0)| ^ p) ≤ C := by
    intro j
    have hsub : (∑ n ∈ S, |(if n ≤ N j then a j n else 0)| ^ p) ≤
        ∑ k ∈ Finset.Ioc 0 (N j), |a j k| ^ p := by
      rw [← Finset.sum_filter_add_sum_filter_not S (fun n => n ≤ N j)]
      have hzero : (∑ n ∈ S.filter (fun n => ¬ n ≤ N j),
          |(if n ≤ N j then a j n else 0)| ^ p) = 0 := by
        apply Finset.sum_eq_zero
        intro n hn
        rw [if_neg (Finset.mem_filter.mp hn).2, abs_zero, zero_pow (by omega)]
      rw [hzero, add_zero]
      calc (∑ n ∈ S.filter (fun n => n ≤ N j), |(if n ≤ N j then a j n else 0)| ^ p)
          = ∑ n ∈ S.filter (fun n => n ≤ N j), |a j n| ^ p :=
            Finset.sum_congr rfl fun n hn => by rw [if_pos (Finset.mem_filter.mp hn).2]
        _ ≤ ∑ k ∈ Finset.Ioc 0 (N j), |a j k| ^ p := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro n hn
              obtain ⟨hnS, hnN⟩ := Finset.mem_filter.mp hn
              exact Finset.mem_Ioc.mpr ⟨(hSprime n hnS).pos, hnN⟩
            · intro _ _ _; exact pow_nonneg (abs_nonneg _) _
    exact hsub.trans (ha j)
  have := le_of_tendsto' hsum hle
  linarith

end RHTower
