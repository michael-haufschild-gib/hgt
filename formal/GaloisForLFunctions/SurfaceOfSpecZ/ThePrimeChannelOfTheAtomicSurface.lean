import GaloisForLFunctions.SurfaceOfSpecZ.TheAtomicSurfaceHasGenusNLogN
import GaloisForLFunctions.HTGeometry.WeightedSchurTest
import GaloisForLFunctions.RHTower.MertensFirst

/-!
# The prime channel of the atomic surface has spectral radius `≍ log N`

In the normalization `y_n = √n x_n` of `TheAtomicSurfaceHasGenusNLogN`, the off-diagonal intersection
of the atomic Frobenius graphs is `ω(|log m − log n|) + w(m, n)`: the archimedean jets and Weil's
prime kernel `w(m, nt) = Λ(t)/√t`. On the degrees `1 ≤ n ≤ N` the jets force a genus of order
`N log N` (`TheAtomicGenusIsNLogN`). The prime kernel is the Hecke operator
`Σ_t Λ(t) t^{−1/2}(T_t + T_t*)`, and its quadratic form satisfies

  `Σ_{m,n ≤ N} |y_m||y_n| w(m, n) ≤ (log N + log 4 + 4) Σ y_n²`   (`primeChannel_le`),

  `Σ_{m,n ≤ N} y_m y_n w(m, n) ≥ ((log N)²/4 − (log 4 + 4)(1 + log N))` at `y_n = n^{−1/2}`, whose
  energy is at most `1 + log N`   (`primeChannel_ge`).

So the prime channel has spectral radius between `(log N)/4 − O(1)` and `log N + O(1)`.

**Mechanism.** The weighted Schur test with weights `n^{−1/2}`: the weighted row sum of `n` is
`n^{−1/2}(Σ_{t ≤ N/n} Λ(t)/t + Σ_{t | n} Λ(t))`, the first sum `log(N/n) + O(1)` by Mertens'
theorem (`RHTower.Mertens.mertens_first`), the second `log n`. The archimedean channel is `N` times
larger: at the atom spacing `1/N` in `log n` the jets see the logarithmic singularity of the
Lévy density, the primes only the pole of `ζ` at `1`. The arithmetic of the zeros is invisible to
atoms in either channel.
-/

open Finset

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ

open ArithmeticEffectivityTheory
open scoped ArithmeticFunction.vonMangoldt

theorem weilPrimeKernel_comm (m n : ℕ) : weilPrimeKernel m n = weilPrimeKernel n m := by
  unfold weilPrimeKernel
  by_cases h1 : m ∣ n ∧ m ≠ n
  · have h2 : ¬ (n ∣ m ∧ n ≠ m) := fun h => h1.2 (Nat.dvd_antisymm h1.1 h.1)
    rw [if_pos h1, if_neg h2, if_pos h1]
  · by_cases h2 : n ∣ m ∧ n ≠ m
    · rw [if_neg h1, if_pos h2, if_pos h2]
    · rw [if_neg h1, if_neg h2, if_neg h2, if_neg h1]

/-- `√t · √(nt) = t √n`. -/
theorem sqrt_mul_sqrt_mul {n t : ℕ} :
    Real.sqrt t * Real.sqrt ((n * t : ℕ) : ℝ) = t * Real.sqrt n := by
  rw [Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg n), ← mul_assoc, mul_comm (Real.sqrt t),
    mul_assoc, Real.mul_self_sqrt (Nat.cast_nonneg t)]
  ring

/-- The multiples of `n` in `[1, N]` are `n t`, `1 ≤ t ≤ N/n`. -/
theorem image_mul_Icc {n N : ℕ} (hn : 0 < n) :
    (Icc 1 (N / n)).image (n * ·) = (Icc 1 N).filter (n ∣ ·) := by
  ext m
  simp only [mem_image, mem_Icc, mem_filter]
  constructor
  · rintro ⟨t, ⟨ht1, ht2⟩, rfl⟩
    refine ⟨⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hn.ne' (by omega)), ?_⟩,
      dvd_mul_right n t⟩
    calc n * t ≤ n * (N / n) := Nat.mul_le_mul_left n ht2
      _ ≤ N := Nat.mul_div_le N n
  · rintro ⟨⟨hm1, hm2⟩, ⟨t, rfl⟩⟩
    refine ⟨t, ⟨?_, ?_⟩, rfl⟩
    · rcases Nat.eq_zero_or_pos t with rfl | h
      · simp at hm1
      · exact h
    · rw [Nat.le_div_iff_mul_le hn, mul_comm]; exact hm2

/-- **The weighted row sum of the prime kernel.** For `1 ≤ n ≤ N`,
`Σ_{m ≤ N} w(n, m) m^{−1/2} ≤ (log N + log 4 + 4) n^{−1/2}`. -/
theorem row_weilPrimeKernel_le {N n : ℕ} (hn : n ∈ Icc 1 N) :
    ∑ m ∈ Icc 1 N, weilPrimeKernel n m * (1 / Real.sqrt m) ≤
      (Real.log N + Real.log 4 + 4) * (1 / Real.sqrt n) := by
  rw [mem_Icc] at hn
  have hn0 : 0 < n := by omega
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn0)
  -- the multiples and the divisors of `n`
  set G : ℕ → ℝ := fun m => if n ∣ m then Λ (m / n) / ((m / n : ℕ) : ℝ) * (1 / Real.sqrt n) else 0
  set D : ℕ → ℝ := fun m => if m ∣ n then Λ (n / m) * (1 / Real.sqrt n) else 0
  have hpt : ∀ m ∈ Icc 1 N, weilPrimeKernel n m * (1 / Real.sqrt m) ≤ G m + D m := by
    intro m hm
    rw [mem_Icc] at hm
    have hm0 : 0 < m := by omega
    have hG0 : 0 ≤ G m := by
      simp only [G]; split_ifs
      · exact mul_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg _))
          (by positivity)
      · exact le_rfl
    have hD0 : 0 ≤ D m := by
      simp only [D]; split_ifs
      · exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
      · exact le_rfl
    unfold weilPrimeKernel
    by_cases h1 : n ∣ m ∧ n ≠ m
    · rw [if_pos h1]
      obtain ⟨t, rfl⟩ := h1.1
      have ht0 : 0 < t := Nat.pos_of_ne_zero (by rintro rfl; simp at hm0)
      have hdiv : n * t / n = t := Nat.mul_div_cancel_left t hn0
      have hG : G (n * t) = Λ t / t * (1 / Real.sqrt n) := by
        simp only [G, if_pos (dvd_mul_right n t), hdiv]
      have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr (by exact_mod_cast ht0)
      have e : Λ t / Real.sqrt t * (1 / Real.sqrt ((n * t : ℕ) : ℝ)) = Λ t / t * (1 / Real.sqrt n) := by
        rw [div_mul_div_comm, mul_one, div_mul_div_comm, mul_one, sqrt_mul_sqrt_mul]
      rw [hdiv, e, ← hG]
      linarith
    · rw [if_neg h1]
      by_cases h2 : m ∣ n ∧ m ≠ n
      · rw [if_pos h2]
        obtain ⟨t, ht⟩ := h2.1
        have hdiv : n / m = t := by rw [ht]; exact Nat.mul_div_cancel_left t hm0
        have hD : D m = Λ t * (1 / Real.sqrt n) := by simp only [D, if_pos h2.1, hdiv]
        have e : Λ t / Real.sqrt t * (1 / Real.sqrt m) = Λ t * (1 / Real.sqrt n) := by
          have ht0 : 0 < t := by
            rcases Nat.eq_zero_or_pos t with rfl | h
            · rw [ht] at hn0; simp at hn0
            · exact h
          have hsq : Real.sqrt t * Real.sqrt m = Real.sqrt n := by
            rw [← Real.sqrt_mul (Nat.cast_nonneg t), ht]; push_cast; ring_nf
          rw [div_mul_div_comm, mul_one, hsq, mul_one_div]
        rw [hdiv, e, ← hD]
        linarith
      · rw [if_neg h2, zero_mul]
        linarith
  have hsumG : ∑ m ∈ Icc 1 N, G m = (∑ t ∈ Icc 1 (N / n), Λ t / t) * (1 / Real.sqrt n) := by
    rw [← sum_filter_add_sum_filter_not (Icc 1 N) (n ∣ ·)]
    have hnot : ∑ m ∈ (Icc 1 N).filter (fun m => ¬ n ∣ m), G m = 0 :=
      sum_eq_zero fun m hm => by simp only [G, if_neg (mem_filter.mp hm).2]
    rw [hnot, add_zero, ← image_mul_Icc hn0,
      sum_image fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hn0 h, sum_mul]
    refine sum_congr rfl fun t _ => ?_
    simp only [G, if_pos (dvd_mul_right n t), Nat.mul_div_cancel_left t hn0]
  have hsumD : ∑ m ∈ Icc 1 N, D m = Real.log n * (1 / Real.sqrt n) := by
    rw [← sum_filter_add_sum_filter_not (Icc 1 N) (· ∣ n)]
    have hnot : ∑ m ∈ (Icc 1 N).filter (fun m => ¬ m ∣ n), D m = 0 :=
      sum_eq_zero fun m hm => by simp only [D, if_neg (mem_filter.mp hm).2]
    have hfil : (Icc 1 N).filter (· ∣ n) = n.divisors := by
      ext m
      simp only [mem_filter, mem_Icc, Nat.mem_divisors]
      constructor
      · rintro ⟨-, h⟩; exact ⟨h, by omega⟩
      · rintro ⟨h, -⟩
        exact ⟨⟨Nat.pos_of_dvd_of_pos h hn0, (Nat.le_of_dvd hn0 h).trans hn.2⟩, h⟩
    rw [hnot, add_zero, hfil]
    calc ∑ m ∈ n.divisors, D m = ∑ m ∈ n.divisors, Λ (n / m) * (1 / Real.sqrt n) :=
          sum_congr rfl fun m hm => by simp only [D, if_pos (Nat.dvd_of_mem_divisors hm)]
      _ = (∑ m ∈ n.divisors, Λ (n / m)) * (1 / Real.sqrt n) := (sum_mul _ _ _).symm
      _ = Real.log n * (1 / Real.sqrt n) := by
          rw [Nat.sum_div_divisors n (fun d => Λ d), ArithmeticFunction.vonMangoldt_sum]
  -- Mertens and `log (N/n) + log n ≤ log N`
  have hNn : 1 ≤ N / n := (Nat.le_div_iff_mul_le hn0).mpr (by omega)
  have hmert := RHTower.Mertens.mertens_first (N / n) hNn
  have hlog : Real.log ((N / n : ℕ) : ℝ) + Real.log n ≤ Real.log N := by
    rw [← Real.log_mul (by exact_mod_cast (show (N / n) ≠ 0 by omega))
      (by exact_mod_cast hn0.ne')]
    exact Real.log_le_log (by positivity) (by exact_mod_cast Nat.div_mul_le_self N n)
  have hbound : ∑ t ∈ Icc 1 (N / n), Λ t / t + Real.log n ≤ Real.log N + Real.log 4 + 4 := by
    have := (abs_le.mp hmert).2
    linarith
  calc ∑ m ∈ Icc 1 N, weilPrimeKernel n m * (1 / Real.sqrt m)
      ≤ ∑ m ∈ Icc 1 N, (G m + D m) := sum_le_sum hpt
    _ = (∑ t ∈ Icc 1 (N / n), Λ t / t + Real.log n) * (1 / Real.sqrt n) := by
        rw [sum_add_distrib, hsumG, hsumD]; ring
    _ ≤ (Real.log N + Real.log 4 + 4) * (1 / Real.sqrt n) :=
        mul_le_mul_of_nonneg_right hbound (by positivity)

/-- **The primes see only `log N`.** -/
theorem primeChannel_le {N : ℕ} (y : ℕ → ℝ) :
    ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, |y m| * |y n| * weilPrimeKernel m n ≤
      (Real.log N + Real.log 4 + 4) * ∑ n ∈ Icc 1 N, y n ^ 2 := by
  have h := GaloisForLFunctions.weighted_double_sum_le_weightedRowBound (ι := Icc 1 N)
    (b := fun r => y r) (w := fun r => 1 / Real.sqrt r) (K := fun r s => weilPrimeKernel r s)
    (H := Real.log N + Real.log 4 + 4)
    (fun r => by
      have := (mem_Icc.mp r.2).1
      have : (0 : ℝ) < r := by exact_mod_cast (show 0 < (r : ℕ) by omega)
      positivity)
    (fun r s => weilPrimeKernel_comm r s) (fun r s => weilPrimeKernel_nonneg r s)
    (fun r => by
      have := row_weilPrimeKernel_le r.2
      rwa [← sum_coe_sort (Icc 1 N)] at this)
  calc ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, |y m| * |y n| * weilPrimeKernel m n
      = ∑ r : Icc 1 N, ∑ s : Icc 1 N, |y r| * |y s| * weilPrimeKernel r s := by
        rw [← sum_coe_sort (Icc 1 N)]
        exact sum_congr rfl fun r _ => (sum_coe_sort (Icc 1 N) _).symm
    _ ≤ (Real.log N + Real.log 4 + 4) * ∑ r : Icc 1 N, y r ^ 2 := h
    _ = (Real.log N + Real.log 4 + 4) * ∑ n ∈ Icc 1 N, y n ^ 2 := by
        rw [sum_coe_sort (Icc 1 N) (fun n => y n ^ 2)]

/-- `log ⌊√N⌋ ≥ ½ log N − log 2`. -/
theorem half_log_le_log_sqrt {N : ℕ} (hN : 1 ≤ N) :
    Real.log N / 2 - Real.log 2 ≤ Real.log (Nat.sqrt N) := by
  have hM1 : 1 ≤ Nat.sqrt N := Nat.le_sqrt.mpr (by omega)
  have hM : (1 : ℝ) ≤ Nat.sqrt N := by exact_mod_cast hM1
  have hlt : (N : ℝ) < ((Nat.sqrt N : ℕ) + 1 : ℝ) * ((Nat.sqrt N : ℕ) + 1) := by
    exact_mod_cast Nat.lt_succ_sqrt N
  have h4 : (N : ℝ) ≤ 4 * ((Nat.sqrt N : ℕ) : ℝ) ^ 2 := by nlinarith
  have := Real.log_le_log (by exact_mod_cast (show 0 < N by omega)) h4
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow,
    show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow] at this
  push_cast at this
  linarith

/-- **Sharpness.** At `y_n = n^{−1/2}` the prime channel is at least `log M (log M − C)`,
`M = ⌊√N⌋`, `C = log 4 + 4`, while `Σ y_n² ≤ 1 + log N`; with `half_log_le_log_sqrt` the Rayleigh
quotient is at least `(log N)/4 − O(1)`. -/
theorem primeChannel_ge {N : ℕ} (hN : 1 ≤ N) :
    Real.log (Nat.sqrt N) * (Real.log (Nat.sqrt N) - (Real.log 4 + 4)) ≤
      ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
        (1 / Real.sqrt m) * (1 / Real.sqrt n) * weilPrimeKernel m n ∧
    ∑ n ∈ Icc 1 N, (1 / Real.sqrt n) ^ 2 ≤ 1 + Real.log N := by
  constructor
  swap
  · have h := harmonic_le_one_add_log N
    rw [harmonic_eq_sum_Icc, Rat.cast_sum] at h
    calc ∑ n ∈ Icc 1 N, (1 / Real.sqrt n) ^ 2 = ∑ n ∈ Icc 1 N, ((n : ℝ))⁻¹ :=
          sum_congr rfl fun n _ => by
            rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg n), one_pow, one_div]
      _ ≤ 1 + Real.log N := by simpa using h
  set M := Nat.sqrt N with hM
  set C : ℝ := Real.log 4 + 4 with hC
  have hM1 : 1 ≤ M := Nat.le_sqrt.mpr (by omega)
  have hMM : M * M ≤ N := Nat.sqrt_le N
  have hMN : M ≤ N := Nat.sqrt_le_self N
  have hterm : ∀ m n : ℕ, 0 ≤ (1 / Real.sqrt m) * (1 / Real.sqrt n) * weilPrimeKernel m n :=
    fun m n => mul_nonneg (by positivity) (weilPrimeKernel_nonneg m n)
  -- the pairs `(n t, n)`
  have hinner : ∀ n ∈ Icc 1 N, (∑ t ∈ Icc 1 (N / n), Λ t / t) * (1 / n) ≤
      ∑ m ∈ Icc 1 N, (1 / Real.sqrt m) * (1 / Real.sqrt n) * weilPrimeKernel m n := by
    intro n hn
    have hn0 : 0 < n := by have := (mem_Icc.mp hn).1; omega
    calc (∑ t ∈ Icc 1 (N / n), Λ t / t) * (1 / n)
        = ∑ m ∈ (Icc 1 N).filter (n ∣ ·),
            (1 / Real.sqrt m) * (1 / Real.sqrt n) * weilPrimeKernel m n := by
          rw [← image_mul_Icc hn0, sum_image fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hn0 h,
            sum_mul]
          refine sum_congr rfl fun t ht => ?_
          have ht0 : 0 < t := by have := (mem_Icc.mp ht).1; omega
          rcases Nat.lt_or_ge t 2 with h2 | h2
          · obtain rfl : t = 1 := by omega
            simp [weilPrimeKernel, ArithmeticFunction.vonMangoldt_apply_one]
          · have hne : n * t ≠ n := by
              intro h
              have : n * t = n * 1 := by rw [h, mul_one]
              have := Nat.eq_of_mul_eq_mul_left hn0 this
              omega
            have hk : weilPrimeKernel (n * t) n = Λ t / Real.sqrt t := by
              rw [weilPrimeKernel_comm, weilPrimeKernel, if_pos ⟨dvd_mul_right n t, hne.symm⟩,
                Nat.mul_div_cancel_left t hn0]
            rw [hk]
            have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn0)
            have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr (by exact_mod_cast ht0)
            have hsnt := sqrt_mul_sqrt_mul (n := n) (t := t)
            have hnn : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt (Nat.cast_nonneg n)
            have hsm : 0 < Real.sqrt ((n * t : ℕ) : ℝ) :=
              Real.sqrt_pos.mpr (by exact_mod_cast Nat.mul_pos hn0 ht0)
            have hden : Real.sqrt t * Real.sqrt ((n * t : ℕ) : ℝ) * Real.sqrt n = t * n := by
              rw [hsnt, mul_assoc, hnn]
            have ht' : (0 : ℝ) < t := by exact_mod_cast ht0
            have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
            calc Λ t / t * (1 / n) = Λ t * (1 / (t * n)) := by
                  rw [div_mul_div_comm, mul_one, mul_one_div]
              _ = Λ t * (1 / (Real.sqrt t * Real.sqrt ((n * t : ℕ) : ℝ) * Real.sqrt n)) := by
                  rw [hden]
              _ = 1 / Real.sqrt ((n * t : ℕ) : ℝ) * (1 / Real.sqrt n) * (Λ t / Real.sqrt t) := by
                  field_simp
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun m _ _ => hterm m n
  -- Mertens from below on `n ≤ √N`, where `N/n ≥ M`
  have hlow : ∀ n ∈ Icc 1 M, max (Real.log M - C) 0 * (1 / (n : ℝ)) ≤
      (∑ t ∈ Icc 1 (N / n), Λ t / t) * (1 / n) := by
    intro n hn
    obtain ⟨hn1, hnM⟩ := mem_Icc.mp hn
    have hn0 : 0 < n := by omega
    have hMn : M ≤ N / n := (Nat.le_div_iff_mul_le hn0).mpr
      ((Nat.mul_le_mul_left M hnM).trans hMM)
    have hsub : ∑ t ∈ Icc 1 M, Λ t / t ≤ ∑ t ∈ Icc 1 (N / n), Λ t / t :=
      sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc le_rfl hMn) fun t _ _ =>
        div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg _)
    have hmert := (abs_le.mp (RHTower.Mertens.mertens_first M hM1)).1
    have hnn : 0 ≤ ∑ t ∈ Icc 1 (N / n), Λ t / t :=
      sum_nonneg fun t _ => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg _)
    refine mul_le_mul_of_nonneg_right (max_le (by linarith) hnn) (by positivity)
  have hsumM : max (Real.log M - C) 0 * Real.log M ≤
      ∑ n ∈ Icc 1 M, max (Real.log M - C) 0 * (1 / (n : ℝ)) := by
    rw [← mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (le_max_right _ _)
    have h := log_add_one_le_harmonic M
    rw [harmonic_eq_sum_Icc, Rat.cast_sum] at h
    have h' : Real.log M ≤ Real.log ((M + 1 : ℕ) : ℝ) :=
      Real.log_le_log (by exact_mod_cast (show 0 < M by omega)) (by exact_mod_cast Nat.le_succ M)
    calc Real.log M ≤ Real.log ((M + 1 : ℕ) : ℝ) := h'
      _ ≤ ∑ n ∈ Icc 1 M, (1 / (n : ℝ)) := by simpa [one_div] using h
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg (by exact_mod_cast hM1)
  have hkey : Real.log M * (Real.log M - C) ≤ max (Real.log M - C) 0 * Real.log M := by
    rcases le_total 0 (Real.log M - C) with h | h
    · rw [max_eq_left h]; ring_nf; exact le_rfl
    · rw [max_eq_right h]; nlinarith
  calc Real.log M * (Real.log M - C) ≤ max (Real.log M - C) 0 * Real.log M := hkey
    _ ≤ ∑ n ∈ Icc 1 M, max (Real.log M - C) 0 * (1 / (n : ℝ)) := hsumM
    _ ≤ ∑ n ∈ Icc 1 M, (∑ t ∈ Icc 1 (N / n), Λ t / t) * (1 / n) := sum_le_sum hlow
    _ ≤ ∑ n ∈ Icc 1 N, (∑ t ∈ Icc 1 (N / n), Λ t / t) * (1 / n) :=
        sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc le_rfl hMN) fun n _ _ =>
          mul_nonneg (sum_nonneg fun t _ =>
            div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg _)) (by positivity)
    _ ≤ ∑ n ∈ Icc 1 N, ∑ m ∈ Icc 1 N,
          (1 / Real.sqrt m) * (1 / Real.sqrt n) * weilPrimeKernel m n := sum_le_sum hinner
    _ = _ := sum_comm

end GaloisForLFunctions.SurfaceOfSpecZ
