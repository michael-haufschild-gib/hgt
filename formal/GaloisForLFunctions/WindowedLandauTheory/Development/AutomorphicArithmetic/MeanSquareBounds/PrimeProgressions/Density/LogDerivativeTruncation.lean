import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.Density.LogDerivativeSeries
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.Density.PoissonWeights
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.Density.PrimeIntervals
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.Density.MangoldtSeriesMass

/-! Truncate a normalized logarithmic derivative to a finite prime interval. -/

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
open scoped Classical

noncomputable section

namespace QH.PrimeProgressions

private theorem poisson_term_eq (c : ℕ → ℂ) (k n : ℕ) (r : ℝ) :
    (r : ℂ) ^ k * (((Λ n : ℝ) : ℂ) * c n * ((Real.log n : ℂ) ^ k / (k.factorial : ℂ)) *
      (n : ℂ) ^ (-((1 + r : ℝ) : ℂ))) = ((Λ n / n * pw k (r * Real.log n) : ℝ) : ℂ) * c n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have e : (n : ℂ) ^ (-((1 + r : ℝ) : ℂ)) = ((Real.exp (-(r * Real.log n)) / n : ℝ) : ℂ) := by
    rw [← ofReal_natCast, ← ofReal_neg, ← ofReal_cpow hn'.le]
    congr 1
    rw [Real.rpow_def_of_pos hn', eq_div_iff hn'.ne']
    nth_rewrite 2 [← Real.exp_log hn']
    rw [← Real.exp_add]; congr 1; ring
  rw [e]
  unfold pw
  push_cast
  ring

private theorem rpow_form (n : ℕ) (hn : 0 < n) (s x : ℝ) :
    x / (n : ℝ) ^ (1 + s) = x / n * Real.exp (-(s * Real.log n)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Real.rpow_add hn', Real.rpow_one, Real.rpow_def_of_pos hn', Real.exp_neg, mul_comm s]
  field_simp

private theorem truncated_term_bound (c : ℕ → ℂ) (hc : ∀ n, ‖c n‖ ≤ 1) {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ) (K k : ℕ)
    (h1 : K ≤ k) (h2 : k ≤ 2 * K) (n : ℕ) :
    ‖((Λ n / n * pw k (r * Real.log n) : ℝ) : ℂ) * c n -
      (if n ∈ primesIoc (Real.exp (δ / 3 * K / r)) (Real.exp (32 / δ * K / r)) then
        (Real.log n : ℂ) * c n / n *
          ((pw k (r * Real.log n) - pw k (r * Real.log (Real.exp (32 / δ * K / r))) : ℝ) : ℂ)
        else 0)‖ ≤
      δ ^ k * (Λ n / (n : ℝ) ^ (1 + r / 2)) +
        (4 * r) ^ k * ((if n.Prime then 0 else Λ n) / (n : ℝ) ^ (3 / 4 : ℝ)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [primesIoc]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hl : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  have hΛ : 0 ≤ Λ n := vonMangoldt_nonneg
  have key : ∀ w : ℝ, 0 ≤ w → ‖((Λ n / n * w : ℝ) : ℂ) * c n‖ ≤ Λ n / n * w := by
    intro w hw
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    exact mul_le_of_le_one_right (by positivity) (hc n)
  have hpw : 0 ≤ pw k (r * Real.log n) := pw_nonneg k (by positivity)
  have fin : ∀ w : ℝ, 0 ≤ w → w ≤ δ ^ k * Real.exp (-(r * Real.log n / 2)) →
      ‖((Λ n / n * w : ℝ) : ℂ) * c n‖ ≤ δ ^ k * (Λ n / (n : ℝ) ^ (1 + r / 2)) := by
    intro w hw h
    refine (key w hw).trans ?_
    rw [rpow_form n hn]
    calc _ ≤ Λ n / n * (δ ^ k * Real.exp (-(r * Real.log n / 2))) := by gcongr
      _ = _ := by ring_nf
  by_cases hp : n.Prime
  · simp only [hp, if_true, zero_div, mul_zero, add_zero]
    split_ifs with hm
    · rw [primesIoc, Finset.mem_filter, Finset.mem_Ioc, Nat.le_floor_iff (Real.exp_pos _).le] at hm
      rw [Real.log_exp]
      have e0 : r * (32 / δ * K / r) = 32 / δ * K := by field_simp
      rw [e0]
      have e : ((Λ n / n * pw k (r * Real.log n) : ℝ) : ℂ) * c n - (Real.log n : ℂ) * c n / n *
          ((pw k (r * Real.log n) - pw k (32 / δ * K) : ℝ) : ℂ) =
          ((Λ n / n * pw k (32 / δ * K) : ℝ) : ℂ) * c n := by
        rw [vonMangoldt_apply_prime hp]; push_cast; ring
      rw [e]
      refine fin _ (pw_nonneg k (by positivity)) ((pw_large K k hδ le_rfl h2).trans ?_)
      have h3 : Real.log n ≤ 32 / δ * K / r := by
        rw [Real.log_le_iff_le_exp hn']; exact hm.1.2
      rw [le_div_iff₀ hr] at h3
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by positivity)
    · rw [sub_zero]
      refine fin _ hpw ?_
      rw [primesIoc, Finset.mem_filter, Finset.mem_Ioc, Nat.le_floor_iff (Real.exp_pos _).le,
        Nat.floor_lt (Real.exp_pos _).le] at hm
      by_cases h4 : Real.exp (δ / 3 * K / r) < n
      · have h5 : Real.exp (32 / δ * K / r) < n := by
          by_contra h6
          exact hm ⟨⟨h4, not_lt.mp h6⟩, hp⟩
        refine pw_large K k hδ ?_ h2
        have h3 := (Real.lt_log_iff_exp_lt hn').mpr h5
        rw [div_lt_iff₀ hr] at h3
        linarith
      · refine pw_small K k hδ (by positivity) ?_ h1
        have h3 := (Real.log_le_iff_le_exp hn').mpr (not_lt.mp h4)
        rw [le_div_iff₀ hr] at h3
        linarith
  · have hm : n ∉ primesIoc (Real.exp (δ / 3 * K / r)) (Real.exp (32 / δ * K / r)) := by
      rw [primesIoc, Finset.mem_filter]; exact fun h => hp h.2
    simp only [hp, hm, if_false, sub_zero]
    refine (key _ hpw).trans (le_add_of_nonneg_of_le (by positivity) ?_)
    have e : (3 / 4 : ℝ) = 1 + (-1 / 4) := by norm_num
    rw [e, rpow_form n hn]
    calc _ ≤ Λ n / n * ((4 * r) ^ k * Real.exp (Real.log n / 4)) := by
          gcongr; exact pw_pp k hr hl
      _ = _ := by ring_nf

private theorem norm_tsum_le_of_close {T P : ℕ → ℂ} {G : ℕ → ℝ} (hP : Summable P)
    (hG : Summable G) (h : ∀ n, ‖T n - P n‖ ≤ G n) :
    ‖∑' n, T n‖ ≤ ‖∑' n, P n‖ + ∑' n, G n := by
  have h1 : Summable fun n => T n - P n := Summable.of_norm_bounded hG h
  have h2 : ∑' n, T n = ∑' n, P n + ∑' n, (T n - P n) := by
    rw [← hP.tsum_add h1]; simp
  rw [h2]
  refine (norm_add_le _ _).trans ?_
  gcongr
  exact tsum_of_norm_bounded hG.hasSum h

theorem poisson_series_le (c : ℕ → ℂ) (hc : ∀ n, ‖c n‖ ≤ 1) {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ) (K k : ℕ)
    (h1 : K ≤ k) (h2 : k ≤ 2 * K) (hs : Summable fun n : ℕ => Λ n / (n : ℝ) ^ (1 + r / 2)) :
    r ^ k * ‖derSeries c k ((1 + r : ℝ) : ℂ)‖ ≤
      ‖∑ n ∈ primesIoc (Real.exp (δ / 3 * K / r)) (Real.exp (32 / δ * K / r)),
        (Real.log n : ℂ) * c n / n *
          ((pw k (r * Real.log n) - pw k (r * Real.log (Real.exp (32 / δ * K / r))) : ℝ) : ℂ)‖ +
      (δ ^ k * ∑' n : ℕ, Λ n / (n : ℝ) ^ (1 + r / 2) +
        (4 * r) ^ k * ∑' n : ℕ, (if n.Prime then 0 else Λ n) / (n : ℝ) ^ (3 / 4 : ℝ)) := by
  have hq := summable_nonPrime_mangoldt_three_quarters
  have hP := hasSum_sum_of_ne_finset_zero
    (s := primesIoc (Real.exp (δ / 3 * K / r)) (Real.exp (32 / δ * K / r)))
    (L := SummationFilter.unconditional ℕ)
    (f := fun n : ℕ => if n ∈ primesIoc (Real.exp (δ / 3 * K / r)) (Real.exp (32 / δ * K / r)) then
        (Real.log n : ℂ) * c n / n *
          ((pw k (r * Real.log n) - pw k (r * Real.log (Real.exp (32 / δ * K / r))) : ℝ) : ℂ)
        else 0) (fun n hn => if_neg hn)
  have h := norm_tsum_le_of_close hP.summable ((hs.mul_left (δ ^ k)).add (hq.mul_left ((4 * r) ^ k)))
    (truncated_term_bound c hc hr hδ K k h1 h2)
  rw [hP.tsum_eq, (hs.mul_left _).tsum_add (hq.mul_left _), tsum_mul_left, tsum_mul_left,
    Finset.sum_congr rfl (fun n hn => if_pos hn)] at h
  refine le_of_eq_of_le ?_ h
  simp_rw [← poisson_term_eq]
  rw [tsum_mul_left, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hr.le, derSeries]

end QH.PrimeProgressions
