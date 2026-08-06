import GaloisForLFunctions.HTGeometry.PrimeSieveDensityTelescope
import GaloisForLFunctions.HTGeometry.PrimeSieveEulerTrace
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The regular polarized determinant of a commuting prime sieve

The polarized regularized determinant of the sieved diagonal operator has
logarithm the odd part of the regularized log-determinant expansion: only the
odd power traces survive the polarization, and the quadratic term that the
regularization removes never appears.  The traces are the sieved zeta values, so
the whole logarithm is an explicit odd power series in the spectral parameter
whose coefficients are the finite Euler products of the sieve.

Three consequences are proved here.  Adjoining one prime replaces the logarithm
by its difference with its own decimation at that prime, which is the exact
prime-enlargement law.  That difference is bounded on every closed subdisk by a
constant times the inverse cube of the adjoined prime, so the enlargement
increments are absolutely summable over all primes.  Along any enumeration of
the primes the sieved traces collapse to the single surviving eigenvalue, and the
logarithm converges to the vacuum logarithm `2t + log(1-t) - log(1+t)`, that is,
the determinant converges to `e^{2t}(1-t)/(1+t)`.
-/

open Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

section Traces

/-- The natural-power trace weight is summable above the abscissa one. -/
theorem summable_natPow_inv {k : ℕ} (hk : 1 < k) :
    Summable fun n : ℕ => (((n : ℕ) : ℝ) ^ k)⁻¹ := by
  simpa [one_div] using (Real.summable_one_div_nat_pow (p := k)).mpr hk

/-- The natural-power trace weight is completely multiplicative. -/
theorem multiplicative_natPow_inv (k m n : ℕ) :
    ((((m * n : ℕ) : ℝ)) ^ k)⁻¹ = (((m : ℕ) : ℝ) ^ k)⁻¹ * (((n : ℕ) : ℝ) ^ k)⁻¹ := by
  push_cast
  rw [mul_pow, mul_inv]

/-- The `k`-th power trace of the sieved diagonal operator. -/
noncomputable def sieveTrace (P : Finset Nat.Primes) (k : ℕ) : ℝ :=
  sievedSum (fun n : ℕ => (((n : ℕ) : ℝ) ^ k)⁻¹) P

/-- **Sieved zeta trace, natural-power form.** -/
theorem sieveTrace_eq_mul_prod {k : ℕ} (hk : 1 < k) (P : Finset Nat.Primes) :
    sieveTrace P k
      = (∑' n : ℕ, (((n : ℕ) : ℝ) ^ k)⁻¹)
        * ∏ p ∈ P, (1 - ((((p : ℕ) : ℝ)) ^ k)⁻¹) :=
  sievedSum_eq_mul_prod (summable_natPow_inv hk) (multiplicative_natPow_inv k) P

/-- **Prime enlargement of the sieved trace.** -/
theorem sieveTrace_insert {k : ℕ} (hk : 1 < k) {p : Nat.Primes}
    {P : Finset Nat.Primes} (hp : p ∉ P) :
    sieveTrace (insert p P) k
      = sieveTrace P k * (1 - ((((p : ℕ) : ℝ)) ^ k)⁻¹) :=
  sievedSum_insert (summable_natPow_inv hk) (multiplicative_natPow_inv k) hp

theorem sieveTrace_nonneg (P : Finset Nat.Primes) (k : ℕ) : 0 ≤ sieveTrace P k := by
  refine tsum_nonneg fun n => ?_
  by_cases h : n ∈ {n : ℕ | Nat.Coprime n (sievePrimorial P)}
  · rw [Set.indicator_of_mem h]
    positivity
  · rw [Set.indicator_of_notMem h]

/-- The universal bound for the odd power traces. -/
noncomputable def sieveTraceBound : ℝ := ∑' n : ℕ, (((n : ℕ) : ℝ) ^ 3)⁻¹

theorem sieveTraceBound_nonneg : 0 ≤ sieveTraceBound :=
  tsum_nonneg fun n => by positivity

theorem natPow_inv_le {k : ℕ} (hk : 3 ≤ k) (n : ℕ) :
    (((n : ℕ) : ℝ) ^ k)⁻¹ ≤ (((n : ℕ) : ℝ) ^ 3)⁻¹ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Nat.cast_zero, zero_pow (by omega), zero_pow (by omega)]
  · have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have h3 : (0 : ℝ) < ((n : ℝ)) ^ 3 := by positivity
    have hle : ((n : ℝ)) ^ 3 ≤ ((n : ℝ)) ^ k := pow_le_pow_right₀ h1 hk
    exact inv_anti₀ h3 hle

/-- Every odd power trace of a sieve is bounded by the third zeta value. -/
theorem sieveTrace_le_bound {k : ℕ} (hk : 3 ≤ k) (P : Finset Nat.Primes) :
    sieveTrace P k ≤ sieveTraceBound := by
  refine Summable.tsum_le_tsum (fun n => ?_)
    ((summable_natPow_inv (by omega)).indicator _) (summable_natPow_inv (by norm_num))
  by_cases h : n ∈ {n : ℕ | Nat.Coprime n (sievePrimorial P)}
  · rw [Set.indicator_of_mem h]
    exact natPow_inv_le hk n
  · rw [Set.indicator_of_notMem h]
    positivity

end Traces

section LogDeterminant

/-- The logarithm of the polarized regularized determinant of the sieved
diagonal operator.  Only the odd power traces survive the polarization, and the
regularized quadratic term is absent. -/
noncomputable def sieveLogPhi (P : Finset Nat.Primes) (t : ℝ) : ℝ :=
  -2 * ∑' j : ℕ, t ^ (2 * j + 3) / ((2 * j + 3 : ℕ) : ℝ) * sieveTrace P (2 * j + 3)

/-- The termwise bound of the logarithmic expansion by a geometric series. -/
theorem norm_sieveLogPhi_term_le (P : Finset Nat.Primes) (t : ℝ) (j : ℕ) :
    ‖t ^ (2 * j + 3) / ((2 * j + 3 : ℕ) : ℝ) * sieveTrace P (2 * j + 3)‖
      ≤ sieveTraceBound * |t| ^ 3 * (|t| ^ 2) ^ j := by
  have hTb : sieveTrace P (2 * j + 3) ≤ sieveTraceBound :=
    sieveTrace_le_bound (by omega) P
  have hT0 : 0 ≤ sieveTrace P (2 * j + 3) := sieveTrace_nonneg P _
  have hden : (1 : ℝ) ≤ ((2 * j + 3 : ℕ) : ℝ) := by
    have : (1 : ℕ) ≤ 2 * j + 3 := by omega
    exact_mod_cast this
  have hpow : |t| ^ (2 * j + 3) = |t| ^ 3 * (|t| ^ 2) ^ j := by
    rw [← pow_mul, ← pow_add]
    ring_nf
  calc ‖t ^ (2 * j + 3) / ((2 * j + 3 : ℕ) : ℝ) * sieveTrace P (2 * j + 3)‖
      = |t| ^ (2 * j + 3) / ((2 * j + 3 : ℕ) : ℝ) * sieveTrace P (2 * j + 3) := by
        rw [Real.norm_eq_abs, abs_mul, abs_div, abs_pow, abs_of_nonneg hT0,
          abs_of_nonneg (by positivity : (0:ℝ) ≤ ((2 * j + 3 : ℕ) : ℝ))]
    _ ≤ |t| ^ (2 * j + 3) * sieveTraceBound := by
        refine mul_le_mul ?_ hTb hT0 (by positivity)
        exact div_le_self (by positivity) hden
    _ = sieveTraceBound * |t| ^ 3 * (|t| ^ 2) ^ j := by rw [hpow]; ring

theorem summable_sieveLogPhi_bound {t : ℝ} (ht : |t| < 1) :
    Summable fun j : ℕ => sieveTraceBound * |t| ^ 3 * (|t| ^ 2) ^ j := by
  refine (summable_geometric_of_lt_one (by positivity) ?_).mul_left _
  calc |t| ^ 2 ≤ |t| ^ 1 := by
        refine pow_le_pow_of_le_one (abs_nonneg t) ht.le (by omega)
    _ = |t| := pow_one _
    _ < 1 := ht

theorem summable_sieveLogPhi_term (P : Finset Nat.Primes) {t : ℝ} (ht : |t| < 1) :
    Summable fun j : ℕ =>
      t ^ (2 * j + 3) / ((2 * j + 3 : ℕ) : ℝ) * sieveTrace P (2 * j + 3) :=
  Summable.of_norm_bounded (summable_sieveLogPhi_bound ht)
    (norm_sieveLogPhi_term_le P t)

/-- **Prime-enlargement law of the polarized determinant.**  Adjoining a prime
replaces the logarithm by its difference with its own decimation at that
prime. -/
theorem sieveLogPhi_insert {p : Nat.Primes} {P : Finset Nat.Primes} (hp : p ∉ P)
    {t : ℝ} (ht : |t| < 1) :
    sieveLogPhi (insert p P) t
      = sieveLogPhi P t - sieveLogPhi P (t / ((p : ℕ) : ℝ)) := by
  have hp2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.2.two_le
  have hppos : (0 : ℝ) < ((p : ℕ) : ℝ) := by linarith
  have htp : |t / ((p : ℕ) : ℝ)| < 1 := by
    rw [abs_div, abs_of_nonneg hppos.le]
    rw [div_lt_one hppos]
    linarith [abs_nonneg t]
  have hs1 := summable_sieveLogPhi_term P ht
  have hs2 := summable_sieveLogPhi_term P htp
  have hterm : ∀ j : ℕ,
      t ^ (2 * j + 3) / ((2 * j + 3 : ℕ) : ℝ) * sieveTrace (insert p P) (2 * j + 3)
        = t ^ (2 * j + 3) / ((2 * j + 3 : ℕ) : ℝ) * sieveTrace P (2 * j + 3)
          - (t / ((p : ℕ) : ℝ)) ^ (2 * j + 3) / ((2 * j + 3 : ℕ) : ℝ)
            * sieveTrace P (2 * j + 3) := by
    intro j
    rw [sieveTrace_insert (by omega) hp, div_pow]
    field_simp
  rw [sieveLogPhi, sieveLogPhi, sieveLogPhi, tsum_congr hterm, hs1.tsum_sub hs2]
  ring

/-- The logarithm is bounded on every closed subdisk by a geometric constant
times the cube of the radius. -/
theorem abs_sieveLogPhi_le (P : Finset Nat.Primes) {r t : ℝ} (hr0 : 0 ≤ r)
    (hr : r < 1) (ht : |t| ≤ r) :
    |sieveLogPhi P t| ≤ 2 * sieveTraceBound / (1 - r ^ 2) * |t| ^ 3 := by
  have habs : |t| < 1 := lt_of_le_of_lt ht hr
  have hr2 : r ^ 2 < 1 := by nlinarith
  have hbound : ∀ j : ℕ,
      ‖t ^ (2 * j + 3) / ((2 * j + 3 : ℕ) : ℝ) * sieveTrace P (2 * j + 3)‖
        ≤ sieveTraceBound * |t| ^ 3 * (r ^ 2) ^ j := by
    intro j
    refine (norm_sieveLogPhi_term_le P t j).trans ?_
    have : (|t| ^ 2) ^ j ≤ (r ^ 2) ^ j := by
      refine pow_le_pow_left₀ (by positivity) ?_ j
      nlinarith [abs_nonneg t]
    exact mul_le_mul_of_nonneg_left this
      (mul_nonneg sieveTraceBound_nonneg (by positivity))
  have hsum : Summable fun j : ℕ => sieveTraceBound * |t| ^ 3 * (r ^ 2) ^ j :=
    (summable_geometric_of_lt_one (by positivity) hr2).mul_left _
  have hcoef0 : (0 : ℝ) ≤ sieveTraceBound * |t| ^ 3 :=
    mul_nonneg sieveTraceBound_nonneg (by positivity)
  have hle : ‖∑' j : ℕ,
      t ^ (2 * j + 3) / ((2 * j + 3 : ℕ) : ℝ) * sieveTrace P (2 * j + 3)‖
      ≤ ∑' j : ℕ, sieveTraceBound * |t| ^ 3 * (r ^ 2) ^ j :=
    tsum_of_norm_bounded hsum.hasSum hbound
  have hgeo : (∑' j : ℕ, sieveTraceBound * |t| ^ 3 * (r ^ 2) ^ j)
      = sieveTraceBound * |t| ^ 3 * (1 - r ^ 2)⁻¹ := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one (by positivity) hr2]
  rw [sieveLogPhi, abs_mul]
  rw [hgeo] at hle
  have h2 : |(-2 : ℝ)| = 2 := by norm_num
  rw [h2]
  have hpos : (0 : ℝ) < 1 - r ^ 2 := by linarith
  rw [Real.norm_eq_abs] at hle
  calc 2 * |∑' j : ℕ,
        t ^ (2 * j + 3) / ((2 * j + 3 : ℕ) : ℝ) * sieveTrace P (2 * j + 3)|
      ≤ 2 * (sieveTraceBound * |t| ^ 3 * (1 - r ^ 2)⁻¹) := by linarith
    _ = 2 * sieveTraceBound / (1 - r ^ 2) * |t| ^ 3 := by field_simp

/-- **Absolute summability of the enlargement increments.**  On every closed
subdisk the increment of adjoining a prime is bounded by a constant, independent
of the sieve and of the prime, times the inverse cube of that prime. -/
theorem abs_sieveLogPhi_insert_sub_le {p : Nat.Primes} {P : Finset Nat.Primes}
    (hp : p ∉ P) {r t : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) (ht : |t| ≤ r) :
    |sieveLogPhi (insert p P) t - sieveLogPhi P t|
      ≤ (2 * sieveTraceBound / (1 - r ^ 2) * r ^ 3) / ((p : ℕ) : ℝ) ^ 3 := by
  have habs : |t| < 1 := lt_of_le_of_lt ht hr
  have hp2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.2.two_le
  have hppos : (0 : ℝ) < ((p : ℕ) : ℝ) := by linarith
  have htp : |t / ((p : ℕ) : ℝ)| ≤ r := by
    rw [abs_div, abs_of_nonneg hppos.le, div_le_iff₀ hppos]
    nlinarith [abs_nonneg t]
  rw [sieveLogPhi_insert hp habs]
  have hsub : sieveLogPhi P t - sieveLogPhi P (t / ((p : ℕ) : ℝ)) - sieveLogPhi P t
      = -sieveLogPhi P (t / ((p : ℕ) : ℝ)) := by ring
  rw [hsub, abs_neg]
  refine (abs_sieveLogPhi_le P hr0 hr htp).trans ?_
  have hcube : |t / ((p : ℕ) : ℝ)| ^ 3 ≤ r ^ 3 / ((p : ℕ) : ℝ) ^ 3 := by
    rw [abs_div, abs_of_nonneg hppos.le, div_pow]
    gcongr
  have hcoef : (0 : ℝ) ≤ 2 * sieveTraceBound / (1 - r ^ 2) := by
    have hden : (0 : ℝ) < 1 - r ^ 2 := by nlinarith
    exact div_nonneg (by linarith [sieveTraceBound_nonneg]) hden.le
  calc 2 * sieveTraceBound / (1 - r ^ 2) * |t / ((p : ℕ) : ℝ)| ^ 3
      ≤ 2 * sieveTraceBound / (1 - r ^ 2) * (r ^ 3 / ((p : ℕ) : ℝ) ^ 3) :=
        mul_le_mul_of_nonneg_left hcube hcoef
    _ = (2 * sieveTraceBound / (1 - r ^ 2) * r ^ 3) / ((p : ℕ) : ℝ) ^ 3 := by ring

end LogDeterminant

section Vacuum

/-- The logarithm of the vacuum polarized determinant `e^{2t}(1-t)/(1+t)`. -/
noncomputable def vacuumLogPhi (t : ℝ) : ℝ :=
  2 * t + Real.log (1 - t) - Real.log (1 + t)

theorem exp_vacuumLogPhi {t : ℝ} (ht : |t| < 1) :
    Real.exp (vacuumLogPhi t) = Real.exp (2 * t) * (1 - t) / (1 + t) := by
  have h1 : (0 : ℝ) < 1 - t := by
    have := abs_lt.mp ht
    linarith [this.2]
  have h2 : (0 : ℝ) < 1 + t := by
    have := abs_lt.mp ht
    linarith [this.1]
  rw [vacuumLogPhi, Real.exp_sub, Real.exp_add, Real.exp_log h1, Real.exp_log h2,
    mul_div_assoc]

/-- The odd tail of the inverse hyperbolic tangent series. -/
theorem hasSum_vacuumSeries {t : ℝ} (ht : |t| < 1) :
    HasSum (fun j : ℕ => t ^ (2 * j + 3) / ((2 * j + 3 : ℕ) : ℝ))
      ((Real.log (1 + t) - Real.log (1 - t)) / 2 - t) := by
  have h := (Real.hasSum_log_sub_log_of_abs_lt_one ht).div_const 2
  have heq : (fun k : ℕ => 2 * (1 / (2 * (k : ℝ) + 1)) * t ^ (2 * k + 1) / 2)
      = fun k : ℕ => t ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℝ) := by
    funext k
    push_cast
    ring
  rw [heq] at h
  have h3 : HasSum (fun j : ℕ => t ^ (2 * (j + 1) + 1) / ((2 * (j + 1) + 1 : ℕ) : ℝ))
      ((Real.log (1 + t) - Real.log (1 - t)) / 2 - t) := by
    refine (hasSum_nat_add_iff
      (f := fun k : ℕ => t ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℝ)) 1).mpr ?_
    have hfin : ((Real.log (1 + t) - Real.log (1 - t)) / 2 - t)
        + ∑ i ∈ Finset.range 1, t ^ (2 * i + 1) / ((2 * i + 1 : ℕ) : ℝ)
        = (Real.log (1 + t) - Real.log (1 - t)) / 2 := by
      simp
    rw [hfin]
    exact h
  have hfun : (fun j : ℕ => t ^ (2 * (j + 1) + 1) / ((2 * (j + 1) + 1 : ℕ) : ℝ))
      = fun j : ℕ => t ^ (2 * j + 3) / ((2 * j + 3 : ℕ) : ℝ) := by
    funext j
    have hidx : 2 * (j + 1) + 1 = 2 * j + 3 := by omega
    rw [hidx]
  rwa [hfun] at h3

/-- The sieved traces collapse to the single surviving eigenvalue along any
enumeration of the primes. -/
theorem tendsto_sieveTrace_sievePrefix (e : ℕ ≃ Nat.Primes) {k : ℕ} (hk : 1 < k) :
    Tendsto (fun m : ℕ => sieveTrace (sievePrefix e m) k) atTop (𝓝 1) := by
  classical
  have hsum : Summable fun n : ℕ => (((n : ℕ) : ℝ) ^ k)⁻¹ := summable_natPow_inv hk
  have hlim : (∑' n : ℕ, (if n = 1 then (1 : ℝ) else 0)) = 1 := by
    simp
  rw [show (1 : ℝ) = ∑' n : ℕ, (if n = 1 then (1 : ℝ) else 0) from hlim.symm]
  refine tendsto_tsum_of_dominated_convergence hsum (fun n => ?_) ?_
  · rcases Nat.lt_or_ge n 2 with hn | hn
    · interval_cases n
      · have hzero : ∀ m : ℕ,
            Set.indicator {n : ℕ | Nat.Coprime n (sievePrimorial (sievePrefix e m))}
              (fun n : ℕ => (((n : ℕ) : ℝ) ^ k)⁻¹) 0 = 0 := by
          intro m
          by_cases h : (0 : ℕ) ∈ {n : ℕ | Nat.Coprime n (sievePrimorial (sievePrefix e m))}
          · rw [Set.indicator_of_mem h, Nat.cast_zero, zero_pow (by omega), inv_zero]
          · rw [Set.indicator_of_notMem h]
        simp [hzero]
      · simp
    · obtain ⟨q, hq, hqn⟩ := Nat.exists_prime_and_dvd (n := n) (by omega)
      set jq : ℕ := e.symm ⟨q, hq⟩ with hjq
      have hne : n ≠ 1 := by omega
      rw [if_neg hne]
      refine Tendsto.congr' ?_ (tendsto_const_nhds (x := (0 : ℝ)) (f := atTop (α := ℕ)))
      filter_upwards [eventually_gt_atTop jq] with m hm
      have hmem : (⟨q, hq⟩ : Nat.Primes) ∈ sievePrefix e m := by
        have hval : (⟨q, hq⟩ : Nat.Primes) = e jq := by
          rw [hjq, Equiv.apply_symm_apply]
        rw [hval]
        simp only [sievePrefix]
        exact Finset.mem_image_of_mem _ (Finset.mem_range.mpr hm)
      have hqM : q ∣ sievePrimorial (sievePrefix e m) := by
        rw [sievePrimorial]
        exact Finset.dvd_prod_of_mem (fun p : Nat.Primes => (p : ℕ)) hmem
      have hnotmem : n ∉ {n : ℕ | Nat.Coprime n (sievePrimorial (sievePrefix e m))} := by
        intro hcop
        have hdvd : q ∣ Nat.gcd n (sievePrimorial (sievePrefix e m)) :=
          Nat.dvd_gcd hqn hqM
        rw [show Nat.gcd n (sievePrimorial (sievePrefix e m)) = 1 from hcop] at hdvd
        exact absurd (Nat.dvd_one.mp hdvd) hq.one_lt.ne'
      rw [Set.indicator_of_notMem hnotmem]
  · refine Filter.Eventually.of_forall fun m => fun n => ?_
    by_cases h : n ∈ {n : ℕ | Nat.Coprime n (sievePrimorial (sievePrefix e m))}
    · rw [Set.indicator_of_mem h, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    · rw [Set.indicator_of_notMem h, norm_zero]
      positivity

/-- **Cofinal vacuum limit of the polarized determinant.**  Along any enumeration
of the primes, the logarithm of the polarized determinant converges to the
vacuum logarithm. -/
theorem tendsto_sieveLogPhi_sievePrefix (e : ℕ ≃ Nat.Primes) {t : ℝ}
    (ht : |t| < 1) :
    Tendsto (fun m : ℕ => sieveLogPhi (sievePrefix e m) t) atTop
      (𝓝 (vacuumLogPhi t)) := by
  have hbase : Tendsto
      (fun m : ℕ => ∑' j : ℕ,
        t ^ (2 * j + 3) / ((2 * j + 3 : ℕ) : ℝ)
          * sieveTrace (sievePrefix e m) (2 * j + 3))
      atTop (𝓝 (∑' j : ℕ, t ^ (2 * j + 3) / ((2 * j + 3 : ℕ) : ℝ))) := by
    refine tendsto_tsum_of_dominated_convergence (summable_sieveLogPhi_bound ht)
      (fun j => ?_) (Filter.Eventually.of_forall fun m => norm_sieveLogPhi_term_le _ t)
    have := (tendsto_sieveTrace_sievePrefix e (k := 2 * j + 3) (by omega)).const_mul
      (t ^ (2 * j + 3) / ((2 * j + 3 : ℕ) : ℝ))
    simpa using this
  have hval : (∑' j : ℕ, t ^ (2 * j + 3) / ((2 * j + 3 : ℕ) : ℝ))
      = (Real.log (1 + t) - Real.log (1 - t)) / 2 - t :=
    (hasSum_vacuumSeries ht).tsum_eq
  have hfin := hbase.const_mul (-2 : ℝ)
  rw [hval] at hfin
  have hval2 : (-2 : ℝ) * ((Real.log (1 + t) - Real.log (1 - t)) / 2 - t)
      = vacuumLogPhi t := by
    rw [vacuumLogPhi]
    ring
  rw [hval2] at hfin
  exact hfin

end Vacuum

end GaloisForLFunctions.HTGeometry
