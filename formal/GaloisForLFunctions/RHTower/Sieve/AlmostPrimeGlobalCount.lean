import GaloisForLFunctions.RHTower.Sieve.MertensSecondSharp
import GaloisForLFunctions.PNTPlus.BrunTitchmarsh
import Mathlib

/-!
# Global almost-prime counts of fixed order

Effective Chebyshev and Hardy--Ramanujan bounds for the global squarefree almost-prime counting
functions of order two and three: `π(N) = O(N/log N)` with one explicit constant valid from
`N = 2` on, the Mertens upper bound `∑_{p ≤ N} 1/p ≤ log log N + K`, and the fixed-order counts
`E₂(N) = O(N (log log N + K)/log N)` and `E₃(N) = O(N (log log N + K)²/log N)`, by the smallest
prime-factor decomposition: a squarefree integer with `k` prime factors has `minFac ^ k ≤ m`, so
the count splits through the dyadic Chebyshev range at exponent `(k-1)/k`.
-/

open Filter
open scoped BigOperators

namespace RHTower.Sieve

/-- Number of primes up to `N` inclusive. -/
def primePiCount (N : ℕ) : ℕ := ((Finset.range (N + 1)).filter Nat.Prime).card

/-- **Effective Chebyshev.**  One explicit constant dominates `π(N) log N / N` from `N = 2` on. -/
theorem exists_primePiCount_le :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N →
      (primePiCount N : ℝ) ≤ C * ((N : ℝ) / Real.log N) := by
  obtain ⟨c₀, hc₀⟩ := (BrunTitchmarsh.card_range_filter_prime_isBigO).isBigOWith
  rw [Asymptotics.isBigOWith_iff, eventually_atTop] at hc₀
  obtain ⟨N₀, hN₀⟩ := hc₀
  refine ⟨max (2 * |c₀| + 1) (Real.log (N₀ + 2)), by positivity, fun N hN => ?_⟩
  have hNR : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlogN : 0 < Real.log N := Real.log_pos (by linarith)
  rcases Nat.lt_or_ge (N + 1) N₀ with hsmall | hbig
  · -- the finite initial segment: `π(N) ≤ N` and `log N ≤ log (N₀ + 2)`
    have hle : primePiCount N ≤ N := by
      unfold primePiCount
      calc ((Finset.range (N + 1)).filter Nat.Prime).card ≤ (Finset.Ioc 1 N).card := by
            apply Finset.card_le_card
            intro x hx
            rw [Finset.mem_filter, Finset.mem_range] at hx
            rw [Finset.mem_Ioc]
            exact ⟨hx.2.one_lt, by omega⟩
        _ = N - 1 := by rw [Nat.card_Ioc]
        _ ≤ N := Nat.sub_le _ _
    have hcrude : (primePiCount N : ℝ) ≤ (N : ℝ) := by exact_mod_cast hle
    have hNlogsmall : Real.log N ≤ Real.log (N₀ + 2) := by
      apply Real.log_le_log (by linarith)
      have : (N : ℝ) ≤ (N₀ : ℝ) := by
        have : N ≤ N₀ := by omega
        exact_mod_cast this
      linarith
    calc (primePiCount N : ℝ) ≤ (N : ℝ) := hcrude
      _ = ((N : ℝ) / Real.log N) * Real.log N := by
          field_simp
      _ ≤ ((N : ℝ) / Real.log N) * Real.log (N₀ + 2) :=
          mul_le_mul_of_nonneg_left hNlogsmall (by positivity)
      _ = Real.log (N₀ + 2) * ((N : ℝ) / Real.log N) := by ring
      _ ≤ max (2 * |c₀| + 1) (Real.log (N₀ + 2)) * ((N : ℝ) / Real.log N) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

  · -- the Chebyshev regime
    have hcheb := hN₀ (N + 1) hbig
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at hcheb
    have hcount : (primePiCount N : ℝ) ≤ |c₀| * |((N + 1 : ℕ) : ℝ) / Real.log ((N + 1 : ℕ) : ℝ)| := by
      calc (primePiCount N : ℝ) =
          |(((Finset.range (N + 1)).filter Nat.Prime).card : ℝ)| := by
            rw [abs_of_nonneg (by positivity)]
            rfl
        _ ≤ c₀ * |((N + 1 : ℕ) : ℝ) / Real.log ((N + 1 : ℕ) : ℝ)| := hcheb
        _ ≤ |c₀| * |((N + 1 : ℕ) : ℝ) / Real.log ((N + 1 : ℕ) : ℝ)| :=
            mul_le_mul_of_nonneg_right (le_abs_self c₀) (abs_nonneg _)
    have hquot : |((N + 1 : ℕ) : ℝ) / Real.log ((N + 1 : ℕ) : ℝ)| ≤ 2 * ((N : ℝ) / Real.log N) := by
      have hN1R : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
      have hlogN1 : 0 < Real.log ((N + 1 : ℕ) : ℝ) := by
        apply Real.log_pos
        push_cast
        linarith
      rw [abs_of_nonneg (by positivity)]
      have h1 : ((N + 1 : ℕ) : ℝ) ≤ 2 * (N : ℝ) := by
        push_cast
        linarith
      have h2 : Real.log N ≤ Real.log ((N + 1 : ℕ) : ℝ) := by
        apply Real.log_le_log (by linarith)
        push_cast
        linarith
      calc ((N + 1 : ℕ) : ℝ) / Real.log ((N + 1 : ℕ) : ℝ) ≤
          (2 * (N : ℝ)) / Real.log ((N + 1 : ℕ) : ℝ) := by gcongr
        _ ≤ (2 * (N : ℝ)) / Real.log N := by
            apply div_le_div_of_nonneg_left (by linarith) hlogN h2
        _ = 2 * ((N : ℝ) / Real.log N) := by ring
    calc (primePiCount N : ℝ) ≤
        |c₀| * |((N + 1 : ℕ) : ℝ) / Real.log ((N + 1 : ℕ) : ℝ)| := hcount
      _ ≤ |c₀| * (2 * ((N : ℝ) / Real.log N)) :=
          mul_le_mul_of_nonneg_left hquot (abs_nonneg _)
      _ = 2 * |c₀| * ((N : ℝ) / Real.log N) := by ring
      _ ≤ max (2 * |c₀| + 1) (Real.log (N₀ + 2)) * ((N : ℝ) / Real.log N) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact le_trans (by linarith) (le_max_left _ _)
/-- Mertens upper constant: `∑_{p ≤ N} 1/p ≤ log log N + K` from `N = 2` on. -/
noncomputable def mertensUpperConst : ℝ :=
  meisselMertensConst + (2 * mertensFirstConst + 1 / 2) / Real.log 2

theorem mertensS_le_logLog_add {N : ℕ} (hN : 2 ≤ N) :
    mertensS N ≤ logLog N + mertensUpperConst := by
  have h := abs_mertensS_sub_logLog_sub_const_le hN
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogN : Real.log 2 ≤ Real.log N := by
    apply Real.log_le_log (by norm_num)
    exact_mod_cast hN
  have hnum : (0 : ℝ) ≤ 2 * mertensFirstConst + 1 / 2 := by
    have hpos : (0 : ℝ) < mertensFirstConst :=
      lt_of_lt_of_le (Real.log_pos (by norm_num : (1 : ℝ) < 4)) (le_max_left _ _)
    linarith
  have hquot : (2 * mertensFirstConst + 1 / 2) / Real.log N ≤
      (2 * mertensFirstConst + 1 / 2) / Real.log 2 :=
    div_le_div_of_nonneg_left hnum hlog2 hlogN
  have habs := (abs_le.mp h).2
  unfold mertensUpperConst
  linarith

/-! ## Fixed-order squarefree counts -/

/-- Global squarefree almost-prime count of fixed order `k`. -/
def squarefreeOmegaCount (k N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).filter fun m => Squarefree m ∧ m.primeFactors.card = k).card

/-- A squarefree number with `k` prime factors dominates the `k`-th power of its least factor. -/
theorem minFac_pow_le_of_squarefree {m k : ℕ} (hm : Squarefree m)
    (hk : m.primeFactors.card = k) : m.minFac ^ k ≤ m := by
  have hprod : ∏ p ∈ m.primeFactors, p = m := Nat.prod_primeFactors_of_squarefree hm
  have hle : ∀ p ∈ m.primeFactors, m.minFac ≤ p := by
    intro p hp
    rw [Nat.mem_primeFactors] at hp
    exact Nat.minFac_le_of_dvd hp.1.two_le hp.2.1
  calc m.minFac ^ k = ∏ _p ∈ m.primeFactors, m.minFac := by
        rw [Finset.prod_const, hk]
    _ ≤ ∏ p ∈ m.primeFactors, p := Finset.prod_le_prod' hle
    _ = m := hprod

/-- Splitting off the least prime factor drops the order by exactly one. -/
theorem primeFactors_card_div_minFac {m k : ℕ} (hm : Squarefree m) (h1 : m ≠ 1)
    (hk : m.primeFactors.card = k + 1) :
    Squarefree (m / m.minFac) ∧ (m / m.minFac).primeFactors.card = k := by
  set p := m.minFac with hp
  have hpprime : p.Prime := Nat.minFac_prime h1
  have hpdvd : p ∣ m := Nat.minFac_dvd m
  have hsplit : p * (m / p) = m := Nat.mul_div_cancel' hpdvd
  have hrdvd : m / p ∣ m := Nat.div_dvd_of_dvd hpdvd
  have hrsf : Squarefree (m / p) := hm.squarefree_of_dvd hrdvd
  have hnotdvd : ¬ p ∣ m / p := by
    intro hcon
    have hsq : p * p ∣ m := by
      obtain ⟨d, hd⟩ := hcon
      refine ⟨d, ?_⟩
      calc m = p * (m / p) := hsplit.symm
        _ = p * (p * d) := by rw [hd]
        _ = p * p * d := by ring
    exact absurd (Nat.isUnit_iff.mp (hm p hsq)) hpprime.ne_one
  have hcop : Nat.Coprime p (m / p) := (Nat.Prime.coprime_iff_not_dvd hpprime).mpr hnotdvd
  have hunion : m.primeFactors = {p} ∪ (m / p).primeFactors := by
    conv_lhs => rw [← hsplit]
    rw [Nat.Coprime.primeFactors_mul hcop, Nat.Prime.primeFactors hpprime]
  have hdisj : Disjoint ({p} : Finset ℕ) (m / p).primeFactors := by
    rw [Finset.disjoint_singleton_left]
    intro hcon
    rw [Nat.mem_primeFactors] at hcon
    exact hnotdvd hcon.2.1
  have hcard : m.primeFactors.card = 1 + (m / p).primeFactors.card := by
    rw [hunion, Finset.card_union_of_disjoint hdisj, Finset.card_singleton]
  refine ⟨hrsf, ?_⟩
  omega

/-- **Least-factor count recursion.**  The order-`(k+1)` count splits through the least prime
factor, which is bounded by the `(k+1)`-st root. -/
theorem squarefreeOmegaCount_succ_le (k N : ℕ) :
    squarefreeOmegaCount (k + 1) N ≤
      ∑ p ∈ (Finset.range (N + 1)).filter (fun p => Nat.Prime p ∧ p ^ (k + 1) ≤ N),
        squarefreeOmegaCount k (N / p) := by
  classical
  unfold squarefreeOmegaCount
  set P : Finset ℕ :=
    (Finset.range (N + 1)).filter (fun p => Nat.Prime p ∧ p ^ (k + 1) ≤ N) with hP
  calc ((Finset.Icc 1 N).filter fun m =>
        Squarefree m ∧ m.primeFactors.card = k + 1).card ≤
      (P.biUnion fun p =>
        ((Finset.Icc 1 (N / p)).filter fun r =>
          Squarefree r ∧ r.primeFactors.card = k).image fun r => p * r).card := by
        apply Finset.card_le_card
        intro m hm
        rw [Finset.mem_filter, Finset.mem_Icc] at hm
        obtain ⟨⟨hm1, hmN⟩, hmsf, hmcard⟩ := hm
        have hmne1 : m ≠ 1 := by
          intro hcon
          rw [hcon] at hmcard
          simp at hmcard
        have hpprime : m.minFac.Prime := Nat.minFac_prime hmne1
        have hpow := minFac_pow_le_of_squarefree hmsf hmcard
        obtain ⟨hrsf, hrcard⟩ := primeFactors_card_div_minFac hmsf hmne1 hmcard
        rw [Finset.mem_biUnion]
        refine ⟨m.minFac, ?_, ?_⟩
        · rw [hP, Finset.mem_filter, Finset.mem_range]
          have hple : m.minFac ≤ N := le_trans (Nat.minFac_le (by omega)) hmN
          exact ⟨by omega, hpprime, le_trans hpow hmN⟩
        · rw [Finset.mem_image]
          refine ⟨m / m.minFac, ?_, Nat.mul_div_cancel' (Nat.minFac_dvd m)⟩
          rw [Finset.mem_filter, Finset.mem_Icc]
          have hr1 : 1 ≤ m / m.minFac := by
            rw [Nat.le_div_iff_mul_le (Nat.minFac_pos m)]
            rw [one_mul]
            exact Nat.minFac_le (by omega)
          exact ⟨⟨hr1, Nat.div_le_div_right hmN⟩, hrsf, hrcard⟩
    _ ≤ ∑ p ∈ P,
        (((Finset.Icc 1 (N / p)).filter fun r =>
          Squarefree r ∧ r.primeFactors.card = k).image fun r => p * r).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ p ∈ P, ((Finset.Icc 1 (N / p)).filter fun r =>
          Squarefree r ∧ r.primeFactors.card = k).card := by
        refine Finset.sum_le_sum fun p _ => ?_
        exact Finset.card_image_le

/-- The order-one count is dominated by the prime-counting function. -/
theorem squarefreeOmegaCount_one_le (N : ℕ) :
    squarefreeOmegaCount 1 N ≤ primePiCount N := by
  unfold squarefreeOmegaCount primePiCount
  apply Finset.card_le_card
  intro m hm
  rw [Finset.mem_filter, Finset.mem_Icc] at hm
  obtain ⟨⟨hm1, hmN⟩, hmsf, hmcard⟩ := hm
  have hmne1 : m ≠ 1 := by
    intro hcon
    rw [hcon] at hmcard
    simp at hmcard
  have hprime : m.Prime := by
    obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hmcard
    have hprod := Nat.prod_primeFactors_of_squarefree hmsf
    rw [hp, Finset.prod_singleton] at hprod
    have hpmem : p ∈ m.primeFactors := by rw [hp]; exact Finset.mem_singleton_self p
    rw [Nat.mem_primeFactors] at hpmem
    rw [← hprod]
    exact hpmem.1
  rw [Finset.mem_filter, Finset.mem_range]
  exact ⟨by omega, hprime⟩

/-! ## The Hardy--Ramanujan bounds -/

theorem squarefreeOmegaCount_le_self (k N : ℕ) : squarefreeOmegaCount k N ≤ N := by
  unfold squarefreeOmegaCount
  calc ((Finset.Icc 1 N).filter fun m =>
      Squarefree m ∧ m.primeFactors.card = k).card ≤ (Finset.Icc 1 N).card :=
        Finset.card_filter_le _ _
    _ = N := by rw [Nat.card_Icc]; omega

/-- The Mertens majorant is bounded below by the contribution of the prime two. -/
theorem half_le_logLog_add_mertensUpperConst {N : ℕ} (hN : 2 ≤ N) :
    1 / 2 ≤ logLog N + mertensUpperConst := by
  have h2mem : 2 ∈ Nat.primesLE N := by
    rw [Nat.mem_primesLE]
    exact ⟨hN, Nat.prime_two⟩
  have hterm : (1 / 2 : ℝ) ≤ mertensS N := by
    have hsum := Finset.single_le_sum
      (f := fun p : ℕ => 1 / (p : ℝ)) (fun i _ => by positivity) h2mem
    calc (1 / 2 : ℝ) = 1 / ((2 : ℕ) : ℝ) := by norm_num
      _ ≤ mertensS N := hsum
  linarith [mertensS_le_logLog_add hN]

/-- Restricted prime reciprocal sums are dominated by the full Mertens sum. -/
theorem sum_one_div_filter_le_mertensS (N : ℕ) (Q : ℕ → Prop) [DecidablePred Q] :
    ∑ p ∈ (Finset.range (N + 1)).filter (fun p => Nat.Prime p ∧ Q p), 1 / (p : ℝ) ≤
      mertensS N := by
  rw [mertensS]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    rw [Finset.mem_filter, Finset.mem_range] at hp
    rw [Nat.mem_primesLE]
    exact ⟨by omega, hp.2.1⟩
  · intro p _ _
    positivity

/-- Natural division loses less than one unit against real division. -/
theorem cast_natDiv_ge_sub_one (N p : ℕ) (hp : 0 < p) :
    (N : ℝ) / p - 1 ≤ ((N / p : ℕ) : ℝ) := by
  have hmod := Nat.div_add_mod N p
  have hlt : N % p < p := Nat.mod_lt N hp
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hcast : (p : ℝ) * ((N / p : ℕ) : ℝ) + ((N % p : ℕ) : ℝ) = (N : ℝ) := by
    exact_mod_cast hmod
  have hltR : ((N % p : ℕ) : ℝ) < p := by exact_mod_cast hlt
  rw [div_sub_one hpR.ne', div_le_iff₀ hpR]
  nlinarith

theorem two_le_natDiv_of_pow_le {N p k : ℕ} (hp : 2 ≤ p) (hpow : p ^ (k + 1) ≤ N)
    (hk : 1 ≤ k) : 2 ≤ N / p := by
  rw [Nat.le_div_iff_mul_le (by omega : 0 < p)]
  calc 2 * p ≤ p ^ k * p := by
        have : 2 ≤ p ^ k := le_trans hp (Nat.le_self_pow (by omega) p)
        exact Nat.mul_le_mul_right p this
    _ = p ^ (k + 1) := by ring
    _ ≤ N := hpow

/-- Logarithmic stability of the least-factor division: with `p^(k+1) ≤ N` and `N` beyond the
`2^(2(k+1))` threshold, the divided scale keeps a definite fraction of `log N`. -/
theorem log_natDiv_ge_of_pow_le {N p k : ℕ} (hk : 1 ≤ k) (hp : 2 ≤ p)
    (hpow : p ^ (k + 1) ≤ N) (hbig : 2 ^ (2 * (k + 1)) ≤ N) :
    (1 / (2 * ((k : ℝ) + 1))) * Real.log N ≤ Real.log ((N / p : ℕ) : ℝ) := by
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hNR : (0 : ℝ) < (N : ℝ) := by
    have : 0 < N := lt_of_lt_of_le (by positivity) hbig
    exact_mod_cast this
  have hlogN : 0 < Real.log N := by
    apply Real.log_pos
    have h4 : (4 : ℕ) ≤ N := by
      calc (4 : ℕ) = 2 ^ (2 : ℕ) := by norm_num
        _ ≤ 2 ^ (2 * (k + 1)) := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ ≤ N := hbig
    exact_mod_cast lt_of_lt_of_le (by norm_num : (1:ℕ) < 4) h4
  -- `log p ≤ log N / (k+1)`
  have hlogp : Real.log p ≤ Real.log N / ((k : ℝ) + 1) := by
    rw [le_div_iff₀ (by positivity : (0:ℝ) < (k : ℝ) + 1)]
    have hpowR : ((p : ℝ)) ^ (k + 1) ≤ (N : ℝ) := by exact_mod_cast hpow
    have := Real.log_le_log (by positivity : (0:ℝ) < ((p:ℝ)) ^ (k+1)) hpowR
    rw [Real.log_pow] at this
    calc Real.log p * ((k : ℝ) + 1) = ((k + 1 : ℕ) : ℝ) * Real.log p := by push_cast; ring
      _ ≤ Real.log N := this
  -- the divided scale dominates `N / (2p)`
  have hdivge : (N : ℝ) / (2 * p) ≤ ((N / p : ℕ) : ℝ) := by
    have hone := cast_natDiv_ge_sub_one N p (by omega)
    have htwo : (2 : ℝ) ≤ (N : ℝ) / p := by
      rw [le_div_iff₀ (by positivity : (0:ℝ) < (p:ℝ))]
      have h2p : 2 * p ≤ p ^ (k + 1) := by
        calc 2 * p ≤ p ^ k * p := Nat.mul_le_mul_right p
              (le_trans hp (Nat.le_self_pow (by omega) p))
          _ = p ^ (k + 1) := by ring
      have : (2 * p : ℕ) ≤ N := le_trans h2p hpow
      exact_mod_cast this
    have : (N : ℝ) / (2 * p) ≤ (N : ℝ) / p - 1 := by
      have hhalf : (N : ℝ) / (2 * p) = ((N : ℝ) / p) / 2 := by
        rw [div_div]
        ring_nf
      rw [hhalf]
      linarith
    linarith
  have hdivpos : (0 : ℝ) < (N : ℝ) / (2 * p) := by positivity
  have hlogdiv := Real.log_le_log hdivpos hdivge
  have hlogsplit : Real.log ((N : ℝ) / (2 * p)) =
      Real.log N - Real.log 2 - Real.log p := by
    rw [Real.log_div hNR.ne' (by positivity), Real.log_mul (by norm_num)
      (by positivity : ((p:ℝ)) ≠ 0)]
    ring
  have hlog2N : Real.log 2 ≤ Real.log N / (2 * ((k : ℝ) + 1)) := by
    rw [le_div_iff₀ (by positivity : (0:ℝ) < 2 * ((k : ℝ) + 1))]
    have hbigR : ((2 : ℝ)) ^ (2 * (k + 1)) ≤ (N : ℝ) := by exact_mod_cast hbig
    have := Real.log_le_log (by positivity) hbigR
    rw [Real.log_pow] at this
    calc Real.log 2 * (2 * ((k : ℝ) + 1)) = ((2 * (k + 1) : ℕ) : ℝ) * Real.log 2 := by
          push_cast; ring
      _ ≤ Real.log N := this
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  calc (1 / (2 * ((k : ℝ) + 1))) * Real.log N ≤
      Real.log N - Real.log 2 - Real.log N / ((k : ℝ) + 1) := by
        have hc : 1 / (2 * ((k : ℝ) + 1)) + 1 / ((k : ℝ) + 1) + 1 / (2 * ((k : ℝ) + 1)) ≤ 1 := by
          have hk2 : (2 : ℝ) ≤ (k : ℝ) + 1 := by linarith
          have hsum2 : 1 / (2 * ((k : ℝ) + 1)) + 1 / (2 * ((k : ℝ) + 1)) =
              1 / ((k : ℝ) + 1) := by
            field_simp
            norm_num
          have hhalf : (1 : ℝ) / ((k : ℝ) + 1) ≤ 1 / 2 :=
            div_le_div_of_nonneg_left (by norm_num) (by norm_num) hk2
          linarith
        have h2 := hlog2N
        have h3 : Real.log N / ((k : ℝ) + 1) + Real.log 2 +
            (1 / (2 * ((k : ℝ) + 1))) * Real.log N ≤ Real.log N := by
          have := mul_le_mul_of_nonneg_right hc hlogN.le
          calc Real.log N / ((k : ℝ) + 1) + Real.log 2 +
              (1 / (2 * ((k : ℝ) + 1))) * Real.log N ≤
              Real.log N / ((k : ℝ) + 1) + Real.log N / (2 * ((k : ℝ) + 1)) +
                (1 / (2 * ((k : ℝ) + 1))) * Real.log N := by linarith
            _ = (1 / (2 * ((k : ℝ) + 1)) + 1 / ((k : ℝ) + 1) +
                1 / (2 * ((k : ℝ) + 1))) * Real.log N := by ring
            _ ≤ 1 * Real.log N := this
            _ = Real.log N := one_mul _
        linarith
      _ ≤ Real.log ((N : ℝ) / (2 * p)) - 0 := by
          rw [hlogsplit]
          linarith [hlogp]
      _ = Real.log ((N : ℝ) / (2 * p)) := by ring
      _ ≤ Real.log ((N / p : ℕ) : ℝ) := hlogdiv

/-- Monotonicity of the Mertens majorant under the least-factor division. -/
theorem logLog_natDiv_le {N p : ℕ} (hdiv2 : 2 ≤ N / p) :
    logLog (N / p) ≤ logLog N := by
  have hNp : (2 : ℝ) ≤ ((N / p : ℕ) : ℝ) := by exact_mod_cast hdiv2
  have hle : N / p ≤ N := Nat.div_le_self N p
  have hleR : ((N / p : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hle
  unfold logLog
  have hinner : Real.log ((N / p : ℕ) : ℝ) ≤ Real.log (N : ℝ) :=
    Real.log_le_log (by linarith) hleR
  have hinnerpos : 0 < Real.log ((N / p : ℕ) : ℝ) :=
    Real.log_pos (by linarith)
  exact Real.log_le_log hinnerpos hinner

/-- **Hardy--Ramanujan induction step.**  A global order-`k` bound propagates through the
least-factor recursion, spending exactly one Mertens factor. -/
theorem exists_squarefreeOmegaCount_succ_bound {k : ℕ} (hk : 1 ≤ k) {Ck : ℝ} (hCk : 0 < Ck)
    (hbound : ∀ M : ℕ, 2 ≤ M → (squarefreeOmegaCount k M : ℝ) ≤
      Ck * ((M : ℝ) * (logLog M + mertensUpperConst) ^ (k - 1) / Real.log M)) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N → (squarefreeOmegaCount (k + 1) N : ℝ) ≤
      C * ((N : ℝ) * (logLog N + mertensUpperConst) ^ k / Real.log N) := by
  classical
  refine ⟨max (2 * ((k : ℝ) + 1) * Ck) (Real.log (2 ^ (2 * (k + 1))) * 2 ^ k),
    lt_max_of_lt_left (by positivity), fun N hN => ?_⟩
  have hNR : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlogN : 0 < Real.log N := Real.log_pos (by linarith)
  have hLK := half_le_logLog_add_mertensUpperConst hN
  have hLKpos : (0 : ℝ) < logLog N + mertensUpperConst := by linarith
  rcases Nat.lt_or_ge N (2 ^ (2 * (k + 1))) with hsmall | hbig
  · -- the finite initial segment
    have hcrude : (squarefreeOmegaCount (k + 1) N : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast squarefreeOmegaCount_le_self (k + 1) N
    have hlogsmall : Real.log N ≤ Real.log (2 ^ (2 * (k + 1))) := by
      apply Real.log_le_log (by linarith)
      have : (N : ℝ) ≤ ((2 ^ (2 * (k + 1)) : ℕ) : ℝ) := by exact_mod_cast hsmall.le
      calc (N : ℝ) ≤ ((2 ^ (2 * (k + 1)) : ℕ) : ℝ) := this
        _ = (2 : ℝ) ^ (2 * (k + 1)) := by push_cast; ring
    have hpow2 : (1 / 2 : ℝ) ^ k ≤ (logLog N + mertensUpperConst) ^ k :=
      pow_le_pow_left₀ (by norm_num) hLK k
    have hfactor : Real.log N ≤
        Real.log (2 ^ (2 * (k + 1))) * 2 ^ k * (logLog N + mertensUpperConst) ^ k := by
      have h2k : (1 : ℝ) ≤ 2 ^ k * (logLog N + mertensUpperConst) ^ k := by
        calc (1 : ℝ) = 2 ^ k * (1 / 2 : ℝ) ^ k := by
              rw [← mul_pow]
              norm_num
          _ ≤ 2 ^ k * (logLog N + mertensUpperConst) ^ k := by
              apply mul_le_mul_of_nonneg_left hpow2 (by positivity)
      calc Real.log N ≤ Real.log (2 ^ (2 * (k + 1))) := hlogsmall
        _ = Real.log (2 ^ (2 * (k + 1))) * 1 := (mul_one _).symm
        _ ≤ Real.log (2 ^ (2 * (k + 1))) * (2 ^ k * (logLog N + mertensUpperConst) ^ k) := by
            apply mul_le_mul_of_nonneg_left h2k
            have : (1 : ℝ) < 2 ^ (2 * (k + 1)) := one_lt_pow₀ (by norm_num) (by omega)
            exact (Real.log_pos this).le
        _ = Real.log (2 ^ (2 * (k + 1))) * 2 ^ k * (logLog N + mertensUpperConst) ^ k := by
            ring
    calc (squarefreeOmegaCount (k + 1) N : ℝ) ≤ (N : ℝ) := hcrude
      _ = (N : ℝ) / Real.log N * Real.log N := by field_simp
      _ ≤ (N : ℝ) / Real.log N *
          (Real.log (2 ^ (2 * (k + 1))) * 2 ^ k * (logLog N + mertensUpperConst) ^ k) :=
          mul_le_mul_of_nonneg_left hfactor (by positivity)
      _ = Real.log (2 ^ (2 * (k + 1))) * 2 ^ k *
          ((N : ℝ) * (logLog N + mertensUpperConst) ^ k / Real.log N) := by
          field_simp
      _ ≤ max (2 * ((k : ℝ) + 1) * Ck) (Real.log (2 ^ (2 * (k + 1))) * 2 ^ k) *
          ((N : ℝ) * (logLog N + mertensUpperConst) ^ k / Real.log N) := by
          apply mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  · -- the recursion regime
    have hrec := squarefreeOmegaCount_succ_le k N
    have hrecR : (squarefreeOmegaCount (k + 1) N : ℝ) ≤
        ∑ p ∈ (Finset.range (N + 1)).filter (fun p => Nat.Prime p ∧ p ^ (k + 1) ≤ N),
          (squarefreeOmegaCount k (N / p) : ℝ) := by
      exact_mod_cast hrec
    have hterm : ∀ p ∈ (Finset.range (N + 1)).filter
        (fun p => Nat.Prime p ∧ p ^ (k + 1) ≤ N),
        (squarefreeOmegaCount k (N / p) : ℝ) ≤
          2 * ((k : ℝ) + 1) * Ck * ((N : ℝ) * (logLog N + mertensUpperConst) ^ (k - 1) /
            Real.log N) * (1 / (p : ℝ)) := by
      intro p hp
      rw [Finset.mem_filter, Finset.mem_range] at hp
      obtain ⟨hpN, hpprime, hppow⟩ := hp
      have hp2 : 2 ≤ p := hpprime.two_le
      have hdiv2 : 2 ≤ N / p := two_le_natDiv_of_pow_le hp2 hppow hk
      have hlogdiv := log_natDiv_ge_of_pow_le hk hp2 hppow hbig
      have hlogdivpos : 0 < Real.log ((N / p : ℕ) : ℝ) := by
        apply Real.log_pos
        have : (2 : ℝ) ≤ ((N / p : ℕ) : ℝ) := by exact_mod_cast hdiv2
        linarith
      have hLKdiv := half_le_logLog_add_mertensUpperConst hdiv2
      have hb := hbound (N / p) hdiv2
      have hcastdiv : ((N / p : ℕ) : ℝ) ≤ (N : ℝ) / p := Nat.cast_div_le
      have hLmono : logLog (N / p) + mertensUpperConst ≤ logLog N + mertensUpperConst := by
        have := logLog_natDiv_le (N := N) (p := p) hdiv2
        linarith
      have hpowmono : (logLog (N / p) + mertensUpperConst) ^ (k - 1) ≤
          (logLog N + mertensUpperConst) ^ (k - 1) :=
        pow_le_pow_left₀ (by linarith) hLmono (k - 1)
      calc (squarefreeOmegaCount k (N / p) : ℝ) ≤
          Ck * (((N / p : ℕ) : ℝ) * (logLog (N / p) + mertensUpperConst) ^ (k - 1) /
            Real.log ((N / p : ℕ) : ℝ)) := hb
        _ ≤ Ck * (((N : ℝ) / p) * (logLog N + mertensUpperConst) ^ (k - 1) /
            ((1 / (2 * ((k : ℝ) + 1))) * Real.log N)) := by
            apply mul_le_mul_of_nonneg_left _ hCk.le
            have hnum : ((N / p : ℕ) : ℝ) * (logLog (N / p) + mertensUpperConst) ^ (k - 1) ≤
                ((N : ℝ) / p) * (logLog N + mertensUpperConst) ^ (k - 1) :=
              mul_le_mul hcastdiv hpowmono (by positivity) (by positivity)
            have hd1 : (0 : ℝ) < (1 / (2 * ((k : ℝ) + 1))) * Real.log N := by positivity
            calc ((N / p : ℕ) : ℝ) * (logLog (N / p) + mertensUpperConst) ^ (k - 1) /
                Real.log ((N / p : ℕ) : ℝ) ≤
                ((N / p : ℕ) : ℝ) * (logLog (N / p) + mertensUpperConst) ^ (k - 1) /
                  ((1 / (2 * ((k : ℝ) + 1))) * Real.log N) :=
                  div_le_div_of_nonneg_left (by positivity) hd1 hlogdiv
              _ ≤ ((N : ℝ) / p) * (logLog N + mertensUpperConst) ^ (k - 1) /
                  ((1 / (2 * ((k : ℝ) + 1))) * Real.log N) := by
                  gcongr
        _ = 2 * ((k : ℝ) + 1) * Ck * ((N : ℝ) * (logLog N + mertensUpperConst) ^ (k - 1) /
            Real.log N) * (1 / (p : ℝ)) := by
            have hpne : ((p : ℝ)) ≠ 0 := by positivity
            field_simp
    have hsum := Finset.sum_le_sum hterm
    have hmertens := sum_one_div_filter_le_mertensS N (fun p => p ^ (k + 1) ≤ N)
    have hmertens2 : mertensS N ≤ logLog N + mertensUpperConst := mertensS_le_logLog_add hN
    have hfront : (0 : ℝ) ≤ 2 * ((k : ℝ) + 1) * Ck *
        ((N : ℝ) * (logLog N + mertensUpperConst) ^ (k - 1) / Real.log N) := by positivity
    calc (squarefreeOmegaCount (k + 1) N : ℝ) ≤
        ∑ p ∈ (Finset.range (N + 1)).filter (fun p => Nat.Prime p ∧ p ^ (k + 1) ≤ N),
          (squarefreeOmegaCount k (N / p) : ℝ) := hrecR
      _ ≤ ∑ p ∈ (Finset.range (N + 1)).filter (fun p => Nat.Prime p ∧ p ^ (k + 1) ≤ N),
          2 * ((k : ℝ) + 1) * Ck * ((N : ℝ) * (logLog N + mertensUpperConst) ^ (k - 1) /
            Real.log N) * (1 / (p : ℝ)) := hsum
      _ = 2 * ((k : ℝ) + 1) * Ck *
          ((N : ℝ) * (logLog N + mertensUpperConst) ^ (k - 1) / Real.log N) *
          ∑ p ∈ (Finset.range (N + 1)).filter (fun p => Nat.Prime p ∧ p ^ (k + 1) ≤ N),
            (1 / (p : ℝ)) := by
          rw [Finset.mul_sum]
      _ ≤ 2 * ((k : ℝ) + 1) * Ck *
          ((N : ℝ) * (logLog N + mertensUpperConst) ^ (k - 1) / Real.log N) *
          (logLog N + mertensUpperConst) := by
          apply mul_le_mul_of_nonneg_left _ hfront
          exact le_trans hmertens hmertens2
      _ = 2 * ((k : ℝ) + 1) * Ck *
          ((N : ℝ) * ((logLog N + mertensUpperConst) ^ (k - 1) *
            (logLog N + mertensUpperConst)) / Real.log N) := by
          field_simp
      _ = 2 * ((k : ℝ) + 1) * Ck *
          ((N : ℝ) * (logLog N + mertensUpperConst) ^ k / Real.log N) := by
          have hpowk : (logLog N + mertensUpperConst) ^ (k - 1) *
              (logLog N + mertensUpperConst) = (logLog N + mertensUpperConst) ^ k := by
            rw [← pow_succ]
            congr 1
            omega
          rw [hpowk]
      _ ≤ max (2 * ((k : ℝ) + 1) * Ck) (Real.log (2 ^ (2 * (k + 1))) * 2 ^ k) *
          ((N : ℝ) * (logLog N + mertensUpperConst) ^ k / Real.log N) := by
          apply mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)

/-- Order-one base of the Hardy--Ramanujan tower. -/
theorem exists_squarefreeOmegaCount_one_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N → (squarefreeOmegaCount 1 N : ℝ) ≤
      C * ((N : ℝ) * (logLog N + mertensUpperConst) ^ (1 - 1) / Real.log N) := by
  obtain ⟨C₁, hC₁, hbound⟩ := exists_primePiCount_le
  refine ⟨C₁, hC₁, fun N hN => ?_⟩
  have h1 := squarefreeOmegaCount_one_le N
  have h1R : (squarefreeOmegaCount 1 N : ℝ) ≤ (primePiCount N : ℝ) := by exact_mod_cast h1
  calc (squarefreeOmegaCount 1 N : ℝ) ≤ (primePiCount N : ℝ) := h1R
    _ ≤ C₁ * ((N : ℝ) / Real.log N) := hbound N hN
    _ = C₁ * ((N : ℝ) * (logLog N + mertensUpperConst) ^ (1 - 1) / Real.log N) := by
        norm_num

/-- **Global order-two Hardy--Ramanujan bound.** -/
theorem exists_squarefreeOmegaCount_two_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N → (squarefreeOmegaCount 2 N : ℝ) ≤
      C * ((N : ℝ) * (logLog N + mertensUpperConst) ^ (1 : ℕ) / Real.log N) := by
  obtain ⟨C₁, hC₁, h₁⟩ := exists_squarefreeOmegaCount_one_bound
  obtain ⟨C₂, hC₂, h₂⟩ := exists_squarefreeOmegaCount_succ_bound (k := 1) le_rfl hC₁ h₁
  exact ⟨C₂, hC₂, h₂⟩

/-- **Global order-three Hardy--Ramanujan bound.** -/
theorem exists_squarefreeOmegaCount_three_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N → (squarefreeOmegaCount 3 N : ℝ) ≤
      C * ((N : ℝ) * (logLog N + mertensUpperConst) ^ (2 : ℕ) / Real.log N) := by
  obtain ⟨C₂, hC₂, h₂⟩ := exists_squarefreeOmegaCount_two_bound
  have h₂' : ∀ M : ℕ, 2 ≤ M → (squarefreeOmegaCount 2 M : ℝ) ≤
      C₂ * ((M : ℝ) * (logLog M + mertensUpperConst) ^ (2 - 1) / Real.log M) := by
    intro M hM
    simpa using h₂ M hM
  obtain ⟨C₃, hC₃, h₃⟩ := exists_squarefreeOmegaCount_succ_bound (k := 2) (by omega) hC₂ h₂'
  exact ⟨C₃, hC₃, h₃⟩

end RHTower.Sieve
