import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.ShortNorms.Statement
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Remove prime powers from a short-interval lower bound for the trivial ray class. -/

open Finset ArithmeticFunction

namespace UpperTheory.T3

private theorem sum_le_card_normPrimes (a : ℕ → ℝ) (d M : ℕ)
    (hl : ∀ n, a n ≤ 2 * vonMangoldt n)
    (hN : ∀ p : ℕ, p.Prime → a p ≠ 0 → GlobalTheory.Mem.An.NormOne d M p) (X Y : ℝ) (hY : 1 ≤ Y) :
    ∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊Y⌋₊, a n ≤
      2 * Real.log Y * ((GlobalTheory.Mem.An.normPrimes d M X Y).card : ℝ) +
        2 * (Chebyshev.psi Y - Chebyshev.theta Y) := by
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun n : ℕ => n.Prime)]
  apply add_le_add
  · have h1 : ∑ n ∈ (Finset.Ioc ⌊X⌋₊ ⌊Y⌋₊).filter (fun n : ℕ => n.Prime), a n =
        ∑ n ∈ GlobalTheory.Mem.An.normPrimes d M X Y, a n := by
      symm
      apply Finset.sum_subset
      · intro p hp
        simp only [GlobalTheory.Mem.An.normPrimes, Finset.mem_filter] at hp ⊢
        exact ⟨hp.1, hp.2.1⟩
      · intro p hp hq
        simp only [GlobalTheory.Mem.An.normPrimes, Finset.mem_filter] at hp hq
        by_contra h
        exact hq ⟨hp.1, hp.2, hN p hp.2 h⟩
    rw [h1, mul_comm, ← nsmul_eq_mul]
    apply Finset.sum_le_card_nsmul
    intro p hp
    simp only [GlobalTheory.Mem.An.normPrimes, Finset.mem_filter, Finset.mem_Ioc] at hp
    have h2 : (p : ℝ) ≤ Y := (Nat.le_floor_iff (by linarith)).1 hp.1.2
    have h3 : Real.log p ≤ Real.log Y :=
      Real.log_le_log (by exact_mod_cast hp.2.1.pos) h2
    have h4 := hl p
    rw [vonMangoldt_apply_prime hp.2.1] at h4
    linarith
  · rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Finset.mul_sum]
    refine le_trans (Finset.sum_le_sum fun n _ => hl n) ?_
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.filter_subset_filter _ (Finset.Ioc_subset_Ioc_left (Nat.zero_le _))
    · intro n _ _
      have := @vonMangoldt_nonneg n
      positivity

private theorem sqrt_le_short_main {A K c B X h : ℝ} (hA : 0 < A) (hK : 0 < K) (hc : 0 < c)
    (hcT : c ≤ 1 / (2 * (1 + A) + 2 + K)) (hB : 4 ≤ B) (hX : 1 ≤ X)
    (hBX : Real.log B ≤ c * Real.sqrt (Real.log X))
    (hh : Real.exp (-c * Real.sqrt (Real.log X)) ≤ h) :
    1 ≤ Real.log X ∧ K * Real.sqrt X ≤ h * X / B ^ A := by
  set s := Real.sqrt (Real.log X) with hs
  have hL : 0 ≤ Real.log X := Real.log_nonneg hX
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hss : s * s = Real.log X := Real.mul_self_sqrt hL
  have hB0 : 0 < B := by linarith
  have hB1 : 1 ≤ Real.log B := by
    rw [Real.le_log_iff_exp_le hB0]
    have := Real.exp_one_lt_d9
    linarith
  set T := 2 * (1 + A) + 2 + K with hT
  have hT0 : 0 < T := by positivity
  have hcT' : c * T ≤ 1 := by rwa [le_div_iff₀ hT0] at hcT
  have hsT : T ≤ s := by
    by_contra h'
    have : c * s < c * T := mul_lt_mul_of_pos_left (not_le.1 h') hc
    linarith
  have hc1 : c ≤ 1 :=
    (le_mul_of_one_le_right hc.le (by linarith only [hT, hA, hK])).trans hcT'
  have hs1 : 1 ≤ s := by linarith
  refine ⟨?_, ?_⟩
  · rw [← hss]
    exact hs1.trans (le_mul_of_one_le_right hs0 hs1)
  have hX0 : 0 < X := by linarith
  have hsq : Real.sqrt X = Real.exp (s * s / 2) := by
    rw [hss, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hX0]
    congr 1; ring
  have hXe : X = Real.exp (s * s) := by rw [hss, Real.exp_log hX0]
  have hcs : c * s ≤ s := mul_le_of_le_one_left hs0 hc1
  have hBA : B ^ A ≤ Real.exp (A * s) := by
    rw [Real.rpow_def_of_pos hB0]
    apply Real.exp_le_exp.2
    linarith only [mul_le_mul_of_nonneg_right (hBX.trans hcs) hA.le]
  have hh' : Real.exp (-s) ≤ h := le_trans (Real.exp_le_exp.2 (by linarith)) hh
  have hKe : K ≤ Real.exp (s * s / 2 - (1 + A) * s) := by
    have he := Real.add_one_le_exp (s * s / 2 - (1 + A) * s)
    have h5 : s * 1 ≤ s * (s / 2 - (1 + A)) := mul_le_mul_of_nonneg_left (by linarith) hs0
    linarith only [he, h5, hsT, hT, hA]
  have hBA0 : 0 < B ^ A := Real.rpow_pos_of_pos hB0 A
  rw [le_div_iff₀ hBA0, hsq]
  calc K * Real.exp (s * s / 2) * B ^ A
      ≤ Real.exp (s * s / 2 - (1 + A) * s) * Real.exp (s * s / 2) * Real.exp (A * s) := by
        gcongr
    _ = Real.exp (-s) * Real.exp (s * s) := by
        simp only [← Real.exp_add]; congr 1; ring
    _ ≤ h * X := by
        rw [← hXe]; gcongr

/-- A Mangoldt lower bound in the trivial ray class gives the corresponding rational
prime count. Prime powers contribute at most a constant times the square root of the scale. -/
theorem shortNorm_of_mangoldt {A c₀ e : ℝ} (hA : 0 < A) (hc₀ : 0 < c₀) (he : 0 < e)
    (hmain : ∀ (d M : ℕ) (X h : ℝ), d.Prime → d % 4 = 3 → 100 ≤ d → 3 ≤ M → 1 ≤ X →
      Real.log (4 * (d : ℝ) * (M : ℝ) ^ 2) ≤ c₀ * Real.sqrt (Real.log X) →
      Real.exp (-c₀ * Real.sqrt (Real.log X)) ≤ h → h ≤ 1 →
      ∃ a : ℕ → ℝ, (∀ n, a n ≤ 2 * vonMangoldt n) ∧
        (∀ p : ℕ, p.Prime → a p ≠ 0 → GlobalTheory.Mem.An.NormOne d M p) ∧
        e * h * X / (4 * (d : ℝ) * (M : ℝ) ^ 2) ^ A ≤ ∑ n ∈ Ioc ⌊X⌋₊ ⌊X * (1 + h)⌋₊, a n) :
    ShortNorm := by
  obtain ⟨C, hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  set K : ℝ := 8 * (|C| + 1) / e with hKdef
  have hK : 0 < K := by positivity
  refine ⟨A, min c₀ (1 / (2 * (1 + A) + 2 + K)), e / 8, hA, lt_min hc₀ (by positivity),
    by positivity, ?_⟩
  intro d M X h hd hd4 hd100 hM hX hB hh hh1
  let B : ℝ := 4 * (d : ℝ) * (M : ℝ) ^ 2
  have hB4 : 4 ≤ B := by
    have hd : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
    have hM : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
    dsimp only [B]
    simpa only [one_pow, mul_one] using
      mul_le_mul (mul_le_mul_of_nonneg_left hd (by norm_num : (0 : ℝ) ≤ 4))
        (pow_le_pow_left₀ zero_le_one hM 2) (by norm_num) (by positivity)
  set c := min c₀ (1 / (2 * (1 + A) + 2 + K)) with hc
  have hc0 : 0 < c := lt_min hc₀ (by positivity)
  have hcc : c * Real.sqrt (Real.log X) ≤ c₀ * Real.sqrt (Real.log X) :=
    mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.sqrt_nonneg _)
  have h0 : 0 < h := lt_of_lt_of_le (Real.exp_pos _) hh
  obtain ⟨a, ha, hN, H1⟩ := hmain d M X h hd hd4 hd100 hM hX (hB.trans hcc)
    ((Real.exp_le_exp.2 (by linarith)).trans hh) hh1
  obtain ⟨hL, hS⟩ := sqrt_le_short_main hA hK hc0 (min_le_right _ _) hB4 hX hB hh
  have hY1 : 1 ≤ X * (1 + h) := hX.trans (le_mul_of_one_le_right
    (zero_le_one.trans hX) (by linarith only [h0]))
  have hY2 : X * (1 + h) ≤ 2 * X := by
    rw [mul_comm (2 : ℝ)]
    exact mul_le_mul_of_nonneg_left (by linarith only [hh1]) (zero_le_one.trans hX)
  have H2 := sum_le_card_normPrimes a d M ha hN X (X * (1 + h)) hY1
  have hlog : Real.log (X * (1 + h)) ≤ 2 * Real.log X := by
    rw [Real.log_mul (by linarith) (by linarith)]
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + h by linarith)
    linarith
  have hsq : Real.sqrt (X * (1 + h)) ≤ 2 * Real.sqrt X := by
    rw [Real.sqrt_le_left (by positivity), mul_pow, Real.sq_sqrt (by linarith)]
    linarith
  have H3 : Chebyshev.psi (X * (1 + h)) - Chebyshev.theta (X * (1 + h)) ≤
      (|C| + 1) * (2 * Real.sqrt X) :=
    (hC _).trans (mul_le_mul (by linarith only [le_abs_self C]) hsq
      (Real.sqrt_nonneg _) (by positivity))
  have hBA0 : 0 < B ^ A := Real.rpow_pos_of_pos (by linarith [hB4]) A
  set N : ℝ := ((GlobalTheory.Mem.An.normPrimes d M X (X * (1 + h))).card : ℝ) with hNdef
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  have H4 : 8 * (|C| + 1) * Real.sqrt X ≤ e * (h * X / B ^ A) := by
    have : 8 * (|C| + 1) * Real.sqrt X = e * (K * Real.sqrt X) := by
      rw [hKdef]; field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left hS he.le
  have H5 : e * h * X / B ^ A = e * (h * X / B ^ A) := by ring
  have H6 : 2 * Real.log (X * (1 + h)) * N ≤ 4 * Real.log X * N := by
    apply mul_le_mul_of_nonneg_right _ hN0
    linarith
  have H7 : e / 8 * h * X / (B ^ A * Real.log X) = e * (h * X / B ^ A) / (8 * Real.log X) := by
    field_simp
  rw [H7, div_le_iff₀ (by linarith)]
  linarith only [H1, H2, H3, H4, H5, H6]

end UpperTheory.T3
