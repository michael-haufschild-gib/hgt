import GaloisForLFunctions.RHTower.MertensSecondPrimeRecipSum
import GaloisForLFunctions.PNTPlus.Consequences

/-!
# Prime-diagonal singular-value asymptotics
-/

namespace RHTower

open Filter Asymptotics
open scoped Topology BigOperators

/-- The prime-diagonal singular-value partial sum `∑_{n ≤ N} 1/p_n`. -/
noncomputable def primeDiagonalSum (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1), ((Nat.nth Nat.Prime n : ℕ) : ℝ)⁻¹

theorem primeDiagonalSum_eq_primeRecipSum (N : ℕ) :
    primeDiagonalSum N = primeRecipSum (Nat.nth Nat.Prime N) := by
  classical
  have hinf : {p : ℕ | Nat.Prime p}.Infinite := Nat.infinite_setOf_prime
  have hfilter : primeRecipSum (Nat.nth Nat.Prime N)
      = ∑ n ∈ (Finset.Icc 0 (Nat.nth Nat.Prime N)).filter Nat.Prime, ((n : ℝ))⁻¹ := by
    rw [primeRecipSum, Finset.sum_filter]
    exact Finset.sum_congr rfl fun n _ => rfl
  rw [primeDiagonalSum, hfilter]
  refine Finset.sum_nbij (fun n => Nat.nth Nat.Prime n) ?_ ?_ ?_ ?_
  · intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨Nat.zero_le _, ?_⟩, Nat.nth_mem_of_infinite hinf n⟩
    rcases Nat.lt_succ_iff.mp (Finset.mem_range.mp hn) with hle
    rcases lt_or_eq_of_le hle with hlt | rfl
    · exact ((Nat.nth_lt_nth hinf).mpr hlt).le
    · exact le_rfl
  · intro a _ b _ hab
    have := (Nat.nth_lt_nth hinf (k := a) (n := b))
    rcases lt_trichotomy a b with h | h | h
    · exact absurd hab (by
        have := (Nat.nth_lt_nth hinf).mpr h
        exact ne_of_lt this)
    · exact h
    · exact absurd hab.symm (by
        have := (Nat.nth_lt_nth hinf).mpr h
        exact ne_of_lt this)
  · intro q hq
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_Icc] at hq
    obtain ⟨⟨-, hqle⟩, hqp⟩ := hq
    refine ⟨Nat.count Nat.Prime q, ?_, ?_⟩
    · simp only [Finset.coe_range, Set.mem_Iio]
      have hcount : Nat.nth Nat.Prime (Nat.count Nat.Prime q) = q := Nat.nth_count hqp
      by_contra hcon
      have hcon' : N + 1 ≤ Nat.count Nat.Prime q := Nat.not_lt.mp hcon
      have hlt : Nat.nth Nat.Prime N < Nat.nth Nat.Prime (Nat.count Nat.Prime q) :=
        (Nat.nth_lt_nth hinf).mpr (by omega)
      rw [hcount] at hlt
      omega
    · exact Nat.nth_count hqp
  · intro n _
    rfl

/-- **Weak-ideal membership.**  The prime-diagonal singular values satisfy `n mu_n -> 0`. -/
theorem tendsto_natCast_div_nthPrime :
    Tendsto (fun n : ℕ => (n : ℝ) / ((Nat.nth Nat.Prime n : ℕ) : ℝ)) atTop (𝓝 0) := by
  have hne : ∀ᶠ n : ℕ in atTop, ((Nat.nth Nat.Prime n : ℕ) : ℝ) ≠ 0 := by
    filter_upwards with n
    have hprime : Nat.Prime (Nat.nth Nat.Prime n) :=
      Nat.nth_mem_of_infinite Nat.infinite_setOf_prime n
    exact_mod_cast hprime.ne_zero
  have hequiv : (fun n : ℕ => ((Nat.nth Nat.Prime n : ℕ) : ℝ)) ~[atTop]
      (fun n : ℕ => (n : ℝ) * Real.log (n : ℝ)) := nth_prime_asymp
  have hratio : Tendsto
      (fun n : ℕ => ((n : ℝ) * Real.log (n : ℝ)) / ((Nat.nth Nat.Prime n : ℕ) : ℝ))
      atTop (𝓝 1) := (Asymptotics.isEquivalent_iff_tendsto_one hne).mp hequiv.symm
  have hlogTop : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hinvlog : Tendsto (fun n : ℕ => (Real.log (n : ℝ))⁻¹) atTop (𝓝 0) :=
    hlogTop.inv_tendsto_atTop
  have hprod := hratio.mul hinvlog
  rw [mul_zero] at hprod
  refine hprod.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop 1] with n hn
  have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hlogn : Real.log (n : ℝ) ≠ 0 := (Real.log_pos hn1).ne'
  field_simp

/-! ## The two normalizations -/

theorem tendsto_log_nthPrime_div :
    Tendsto (fun n : ℕ => Real.log ((Nat.nth Nat.Prime n : ℕ) : ℝ) / Real.log (n : ℝ))
      atTop (𝓝 1) := by
  have hequiv : (fun n : ℕ => Real.log ((nth_prime n : ℕ) : ℝ)) ~[atTop]
      (fun n : ℕ => Real.log (n : ℝ)) := log_nth_prime_asymp
  refine (Asymptotics.isEquivalent_iff_tendsto_one ?_).mp hequiv
  filter_upwards [Filter.eventually_gt_atTop 1] with n hn
  have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  exact (Real.log_pos hn1).ne'

theorem tendsto_logLog_nthPrime_sub :
    Tendsto (fun n : ℕ => Real.log (Real.log ((Nat.nth Nat.Prime n : ℕ) : ℝ)) -
      Real.log (Real.log (n : ℝ))) atTop (𝓝 0) := by
  have hdiv := tendsto_log_nthPrime_div
  have hlog := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hdiv
  rw [Real.log_one] at hlog
  refine hlog.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop 2] with n hn
  have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
  have hlogn : 0 < Real.log (n : ℝ) := Real.log_pos hn1
  have hp : 1 < (Nat.nth Nat.Prime n : ℕ) := by
    have hprime : Nat.Prime (Nat.nth Nat.Prime n) :=
      Nat.nth_mem_of_infinite Nat.infinite_setOf_prime n
    exact hprime.one_lt
  have hpr : (1 : ℝ) < ((Nat.nth Nat.Prime n : ℕ) : ℝ) := by exact_mod_cast hp
  have hlogp : 0 < Real.log ((Nat.nth Nat.Prime n : ℕ) : ℝ) := Real.log_pos hpr
  simp only [Function.comp_apply]
  rw [Real.log_div hlogp.ne' hlogn.ne']

theorem tendsto_primeDiagonalSum_sub_logLog :
    Tendsto (fun N : ℕ => primeDiagonalSum N - Real.log (Real.log (N : ℝ))) atTop
      (𝓝 mertensSecondConstant) := by
  have hnth : Tendsto (fun N : ℕ => Nat.nth Nat.Prime N) atTop atTop := by
    refine tendsto_atTop_mono (fun n => ?_) tendsto_id
    exact Nat.le_nth fun hf => absurd hf Nat.infinite_setOf_prime
  have hmertens := tendsto_primeRecipSum_sub_logLog.comp hnth
  have hsum := hmertens.add tendsto_logLog_nthPrime_sub
  rw [add_zero] at hsum
  refine hsum.congr fun N => ?_
  simp only [Function.comp_apply, primeDiagonalSum_eq_primeRecipSum]
  ring

/-- **The ordinary Dixmier normalization vanishes.** -/
theorem tendsto_primeDiagonalSum_div_log :
    Tendsto (fun N : ℕ => primeDiagonalSum N / Real.log (N : ℝ)) atTop (𝓝 0) := by
  have hlogTop : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hA : Tendsto
      (fun N : ℕ => (primeDiagonalSum N - Real.log (Real.log (N : ℝ))) / Real.log (N : ℝ))
      atTop (𝓝 0) := tendsto_primeDiagonalSum_sub_logLog.div_atTop hlogTop
  have hB : Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ))
      atTop (𝓝 0) := by
    have hcomp := (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero).comp hlogTop
    exact hcomp
  have hsum := hA.add hB
  rw [add_zero] at hsum
  refine hsum.congr fun N => ?_
  rw [← add_div]
  congr 1
  ring

/-- **The double-logarithmic normalization is exactly one.** -/
theorem tendsto_primeDiagonalSum_div_logLog :
    Tendsto (fun N : ℕ => primeDiagonalSum N / Real.log (Real.log (N : ℝ))) atTop (𝓝 1) := by
  have hlogTop : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglogTop : Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hlogTop
  have hA : Tendsto
      (fun N : ℕ => (primeDiagonalSum N - Real.log (Real.log (N : ℝ))) /
        Real.log (Real.log (N : ℝ))) atTop (𝓝 0) :=
    tendsto_primeDiagonalSum_sub_logLog.div_atTop hloglogTop
  have hsum := hA.add (tendsto_const_nhds (x := (1 : ℝ)))
  rw [zero_add] at hsum
  refine hsum.congr' ?_
  filter_upwards [hloglogTop.eventually_gt_atTop 0] with N hN
  rw [div_add' _ _ _ hN.ne']
  congr 1
  ring

end RHTower
