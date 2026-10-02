import GaloisForLFunctions.RHTower.PMPowerDampedMobiusRamanujanLogMass
import GaloisForLFunctions.RHTower.EulerDeletionQuasiShuffleConvergence
import GaloisForLFunctions.RHTower.Sieve.TotientMoebiusNormalisation
import GaloisForLFunctions.RHTower.EulerDeletionCoprimeCrossCompletion

open MeasureTheory Set Filter Topology Complex ArithmeticFunction
open scoped BigOperators
noncomputable section
namespace RHTower

def pmRamanujanPrimitive (q N : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, d4BMRamanujanNaturalCoefficient n q

theorem pm_ramanujan_weighted_sum (f : ℕ → ℂ) (N q : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, f n * d4BMRamanujanNaturalCoefficient n q) =
      ∑ x ∈ q.divisorsAntidiagonal, (x.1 : ℂ)*(moebius x.2 : ℂ) *
        ∑ n ∈ Finset.Icc 1 N, if x.1 ∣ n then f n else 0 := by
  calc
    _ = ∑ n ∈ Finset.Icc 1 N, ∑ x ∈ q.divisorsAntidiagonal,
        (x.1 : ℂ)*(moebius x.2 : ℂ)*(if x.1 ∣ n then f n else 0) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [pm_ramanujan_eq_antidiagonal (by have := (Finset.mem_Icc.mp hn).1; omega), Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      split_ifs <;> ring
    _ = _ := by rw [Finset.sum_comm]; simp_rw [← Finset.mul_sum]

theorem pmRamanujanPrimitive_eq_floor (q N : ℕ) :
    pmRamanujanPrimitive q N =
      ∑ x ∈ q.divisorsAntidiagonal,
        (x.1 : ℂ)*(moebius x.2 : ℂ)*((N/x.1 : ℕ) : ℂ) := by
  simpa only [one_mul, pmRamanujanPrimitive, pm_sum_dvd_indicator] using
    pm_ramanujan_weighted_sum (fun _ => 1) N q

theorem pmRamanujanPrimitive_period_sum {q : ℕ} (hq : 1 < q) :
    pmRamanujanPrimitive q q = 0 := by
  rw [pmRamanujanPrimitive_eq_floor]
  have ht (x : ℕ × ℕ) (hx : x ∈ q.divisorsAntidiagonal) :
      (x.1 : ℂ)*(moebius x.2 : ℂ)*((q/x.1 : ℕ) : ℂ) =
        (q : ℂ)*(moebius x.2 : ℂ) := by
    have hdiv := Nat.dvd_of_mem_divisors (Nat.fst_mem_divisors_of_mem_antidiagonal hx)
    have hm : (x.1 : ℂ)*((q/x.1 : ℕ) : ℂ) = (q : ℂ) := by
      exact_mod_cast Nat.mul_div_cancel' hdiv
    calc
      _ = ((x.1 : ℂ)*((q/x.1 : ℕ) : ℂ))*(moebius x.2 : ℂ) := by ring
      _ = _ := by rw [hm]
  rw [Finset.sum_congr rfl ht, ← Finset.mul_sum, pm_mobius_antidiagonal_sum]
  simp [ne_of_gt hq]

theorem pm_twice_sum_Icc_natCast (N : ℕ) :
    2*(∑ n ∈ Finset.Icc 1 N, (n : ℂ)) = (N : ℂ)*((N : ℂ)+1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    push_cast
    linear_combination ih

theorem pm_twice_sum_Icc_dvd_natCast {q d : ℕ} (hd : 0 < d) (hdq : d ∣ q) :
    2*(∑ n ∈ Finset.Icc 1 q, if d ∣ n then (n : ℂ) else 0) =
      (q : ℂ)*(((q/d : ℕ) : ℂ)+1) := by
  classical
  rw [← Finset.sum_filter, sum_Icc_filter_dvd_reindex d q hd (fun n => (n : ℂ))]
  simp_rw [Nat.cast_mul]
  rw [← Finset.mul_sum]
  have hm : (d : ℂ)*((q/d : ℕ) : ℂ) = (q : ℂ) := by
    exact_mod_cast Nat.mul_div_cancel' hdq
  calc
    _ = (d : ℂ)*(2*∑ n ∈ Finset.Icc 1 (q/d), (n : ℂ)) := by ring
    _ = _ := by rw [pm_twice_sum_Icc_natCast, ← mul_assoc, hm]

theorem pm_totient_antidiagonal {q : ℕ} (hq : 0 < q) :
    (∑ x ∈ q.divisorsAntidiagonal, (x.1 : ℂ)*(moebius x.2 : ℂ)) = (q.totient : ℂ) := by
  rw [Nat.sum_divisorsAntidiagonal' (fun a b => (a : ℂ)*(moebius b : ℂ))]
  have h := Sieve.totient_eq_sum_moebius_mul q hq
  have hc := congrArg (fun r : ℝ => (r : ℂ)) h
  push_cast at hc
  simpa only [mul_comm] using hc.symm

theorem pm_ramanujan_first_moment {q : ℕ} (hq : 1 < q) :
    2*(∑ n ∈ Finset.Icc 1 q, (n : ℂ)*d4BMRamanujanNaturalCoefficient n q) =
      (q : ℂ)*(q.totient : ℂ) := by
  rw [pm_ramanujan_weighted_sum (fun n => (n : ℂ)) q q, Finset.mul_sum]
  have ht (x : ℕ × ℕ) (hx : x ∈ q.divisorsAntidiagonal) :
      2*((x.1 : ℂ)*(moebius x.2 : ℂ)*
        ∑ n ∈ Finset.Icc 1 q, if x.1 ∣ n then (n : ℂ) else 0) =
      (q : ℂ)^2*(moebius x.2 : ℂ)+(q : ℂ)*((x.1 : ℂ)*(moebius x.2 : ℂ)) := by
    have hdmem := Nat.fst_mem_divisors_of_mem_antidiagonal hx
    have hd := Nat.pos_of_mem_divisors hdmem
    have hdq := Nat.dvd_of_mem_divisors hdmem
    have hm : (x.1 : ℂ)*((q/x.1 : ℕ) : ℂ) = (q : ℂ) := by
      exact_mod_cast Nat.mul_div_cancel' hdq
    calc
      _ = (x.1 : ℂ)*(moebius x.2 : ℂ)*
          (2*∑ n ∈ Finset.Icc 1 q, if x.1 ∣ n then (n : ℂ) else 0) := by ring
      _ = _ := by
        rw [pm_twice_sum_Icc_dvd_natCast hd hdq]
        linear_combination (q : ℂ)*(moebius x.2 : ℂ)*hm
  rw [Finset.sum_congr rfl ht, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, pm_mobius_antidiagonal_sum,
    pm_totient_antidiagonal (by omega)]
  simp [ne_of_gt hq]

theorem pm_sum_cumulative_eq_first_moment (f : ℕ → ℂ) (N : ℕ) :
    (∑ k ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 k, f n) =
      ((N : ℂ)+1)*(∑ n ∈ Finset.Icc 1 N, f n) -
        ∑ n ∈ Finset.Icc 1 N, (n : ℂ)*f n := by
  induction N with
  | zero => simp
  | succ N ih =>
    simp only [Finset.sum_Icc_succ_top (a := 1) (b := N) (by omega)]
    rw [ih]
    push_cast
    ring

theorem pmRamanujanPrimitive_period_mean {q : ℕ} (hq : 1 < q) :
    (∑ N ∈ Finset.Icc 1 q, pmRamanujanPrimitive q N) =
      -(q : ℂ)*(q.totient : ℂ)/2 := by
  simp only [pmRamanujanPrimitive]
  rw [pm_sum_cumulative_eq_first_moment]
  change ((q : ℂ)+1)*pmRamanujanPrimitive q q - _ = _
  rw [pmRamanujanPrimitive_period_sum hq]
  have h := pm_ramanujan_first_moment hq
  linear_combination -h/2

theorem pm_ramanujan_periodic (q n : ℕ) :
    d4BMRamanujanNaturalCoefficient (n+q) q = d4BMRamanujanNaturalCoefficient n q := by
  simp [d4BMRamanujanNaturalCoefficient, Nat.cast_add]

theorem pmRamanujanPrimitive_succ (q N : ℕ) :
    pmRamanujanPrimitive q (N+1) = pmRamanujanPrimitive q N +
      d4BMRamanujanNaturalCoefficient (N+1) q := by
  exact Finset.sum_Icc_succ_top (by omega) _

theorem pmRamanujanPrimitive_periodic {q : ℕ} (hq : 1 < q) (N : ℕ) :
    pmRamanujanPrimitive q (N+q) = pmRamanujanPrimitive q N := by
  induction N with
  | zero => simpa [pmRamanujanPrimitive] using pmRamanujanPrimitive_period_sum hq
  | succ N ih =>
    rw [show N+1+q = (N+q)+1 by omega, pmRamanujanPrimitive_succ, ih,
      show N+q+1 = (N+1)+q by omega, pm_ramanujan_periodic, pmRamanujanPrimitive_succ]

def pmRamanujanPrimitiveBound (q : ℕ) : ℝ :=
  ∑ n ∈ Finset.range q, ‖pmRamanujanPrimitive q n‖

theorem norm_pmRamanujanPrimitive_le {q : ℕ} (hq : 1 < q) (N : ℕ) :
    ‖pmRamanujanPrimitive q N‖ ≤ pmRamanujanPrimitiveBound q := by
  have hp : Function.Periodic (pmRamanujanPrimitive q) q := pmRamanujanPrimitive_periodic hq
  rw [← hp.map_mod_nat N]
  exact Finset.single_le_sum (fun _ _ => norm_nonneg _)
    (Finset.mem_range.mpr (Nat.mod_lt N (by omega)))

theorem tendsto_pmRamanujanPrimitive_mean_complex {q : ℕ} (hq : 1 < q) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N, pmRamanujanPrimitive q n)/(N : ℂ))
      atTop (𝓝 (-(q.totient : ℂ)/2)) := by
  let f : ℕ → ℂ := fun n => pmRamanujanPrimitive q (n+1)+(q.totient : ℂ)/2
  have hf : Function.Periodic f q := by
    intro n
    dsimp only [f]
    rw [show n+q+1 = (n+1)+q by omega, pmRamanujanPrimitive_periodic hq]
  have hsum (N : ℕ) : (∑ n ∈ Finset.range N, f n) =
      (∑ n ∈ Finset.Icc 1 N, pmRamanujanPrimitive q n)+(N : ℂ)*(q.totient : ℂ)/2 := by
    dsimp only [f]
    rw [Finset.sum_add_distrib, ← sum_Icc_eq_sum_range_succ (pmRamanujanPrimitive q) N]
    simp
    ring
  have hz : (∑ n ∈ Finset.range q, f n) = 0 := by
    rw [hsum, pmRamanujanPrimitive_period_mean hq]
    ring
  obtain ⟨C, hC⟩ := DeletionChronologicalLimit.periodic_zero_sum_prefix_bound
    (by omega : 0 < q) hf hz
  have hlim : Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, f n)/(N : ℂ))
      atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun N => ?_)
      (show Tendsto (fun N : ℕ => C/(N : ℝ)) atTop (𝓝 0) from
        tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop)
    simp only [norm_div, Complex.norm_natCast]
    exact div_le_div_of_nonneg_right (hC N) (Nat.cast_nonneg N)
  have he : ∀ᶠ N : ℕ in atTop,
      (∑ n ∈ Finset.range N, f n)/(N : ℂ)-(q.totient : ℂ)/2 =
        (∑ n ∈ Finset.Icc 1 N, pmRamanujanPrimitive q n)/(N : ℂ) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
    rw [hsum]
    field_simp
    ring
  simpa only [zero_sub, neg_div] using (hlim.sub tendsto_const_nhds).congr' he

theorem tendsto_pmRamanujanPrimitive_mean {q : ℕ} (hq : 1 < q) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N, (pmRamanujanPrimitive q n).re)/(N : ℝ))
      atTop (𝓝 (-(q.totient : ℝ)/2)) := by
  have h := Complex.continuous_re.continuousAt.tendsto.comp
    (tendsto_pmRamanujanPrimitive_mean_complex hq)
  have hv : (-(q.totient : ℂ)/2).re = -(q.totient : ℝ)/2 := by
    norm_num [Complex.div_re]
  rw [hv] at h
  simpa only [Function.comp_def, ← Complex.ofReal_natCast, Complex.div_ofReal_re,
    Complex.re_sum] using h

theorem tendsto_pmRamanujanPrimitive_harmonic {q : ℕ} (hq : 1 < q) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N, (pmRamanujanPrimitive q n).re/(n : ℝ))/
      Real.log N) atTop (𝓝 (-(q.totient : ℝ)/2)) :=
  pm_tendsto_harmonic_average_of_mean (tendsto_pmRamanujanPrimitive_mean hq)

end RHTower
