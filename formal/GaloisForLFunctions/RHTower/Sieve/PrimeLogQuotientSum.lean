import GaloisForLFunctions.RHTower.Sieve.MertensBlock
import GaloisForLFunctions.RHTower.Sieve.HarmonicLogBound

/-!
# The prime sum weighted by the reciprocal logarithm of the quotient

The error of the second application of the averaged recursion is governed by

`∑_{p ≤ N} (log p)/(p · log⌊N/p⌋)`,

and the point is that this is `O(log log N)` rather than `O(log N)`.  The decomposition that shows it
needs no real powers: group the primes by the **dyadic size of the quotient**,

`{p : Nat.log 2 ⌊N/p⌋ = j} ⊆ (⌊N/2^{j+1}⌋, ⌊N/2^j⌋]`,

an interval of integers with integer endpoints, because `2^j ≤ ⌊N/p⌋ ↔ p ≤ ⌊N/2^j⌋`.  On that interval
`log⌊N/p⌋ ≥ j log 2`, while Mertens' first theorem on a block bounds its mass by `log 3 + O(1)` — the two
endpoints being within a factor `3` of each other.  Each dyadic scale therefore contributes `O(1/j)`, and
the number of scales is `⌊log₂ N⌋`, so the harmonic sum gives the `log log`.
-/

noncomputable section
namespace RHTower.Sieve
open Finset

/-- A power of two is at most the quotient exactly when the divisor is at most the reciprocal
quotient. -/
theorem two_pow_le_div_iff {N p j : ℕ} (hp : 1 ≤ p) :
    2 ^ j ≤ N / p ↔ p ≤ N / 2 ^ j := by
  rw [Nat.le_div_iff_mul_le (by positivity : 0 < p),
    Nat.le_div_iff_mul_le (by positivity : 0 < 2 ^ j)]
  constructor
  · intro h
    linarith [h, Nat.mul_comm (2 ^ j) p]
  · intro h
    linarith [h, Nat.mul_comm p (2 ^ j)]

/-- The fibre of the dyadic scale of the quotient is an interval of integers. -/
theorem logQuotient_fiber_subset {N j : ℕ} :
    {p ∈ Finset.Icc 1 N | Nat.Prime p ∧ Nat.log 2 (N / p) = j}
      ⊆ Finset.Ioc (N / 2 ^ (j + 1)) (N / 2 ^ j) := by
  intro p hp
  rw [Finset.mem_filter, Finset.mem_Icc] at hp
  obtain ⟨⟨hp1, hpN⟩, hprime, hlog⟩ := hp
  have hq1 : 1 ≤ N / p := (Nat.one_le_div_iff (by omega)).2 hpN
  have hq0 : N / p ≠ 0 := by omega
  have hlow : 2 ^ j ≤ N / p := by
    rw [← hlog]
    exact Nat.pow_log_le_self 2 hq0
  have hhigh : N / p < 2 ^ (j + 1) := by
    rw [← hlog]
    exact Nat.lt_pow_succ_log_self (by norm_num) _
  rw [Finset.mem_Ioc]
  refine ⟨?_, (two_pow_le_div_iff hp1).1 hlow⟩
  by_contra hcon
  rw [not_lt] at hcon
  exact absurd ((two_pow_le_div_iff hp1).2 hcon) (not_le.mpr hhigh)

/-- The two dyadic endpoints are within a factor `2` and one unit. -/
theorem div_two_pow_le {N j : ℕ} : N / 2 ^ j ≤ 2 * (N / 2 ^ (j + 1)) + 1 := by
  have hhalf : N / 2 ^ (j + 1) = N / 2 ^ j / 2 := by
    rw [Nat.div_div_eq_div_mul, ← pow_succ]
  rw [hhalf]
  omega

/-- **The mass of one dyadic fibre is bounded.**  Mertens on the block, with the endpoints within a
factor `3` of each other. -/
theorem sum_logQuotientFiber_prime_log_div_le (N j : ℕ) :
    (∑ p ∈ Finset.Icc 1 N with (Nat.Prime p ∧ Nat.log 2 (N / p) = j),
        Real.log (p : ℝ) / (p : ℝ))
      ≤ Real.log 3 + 2 * ((Real.log 4 + 4) + (8 + RHTower.Mertens.mertensTail)) := by
  classical
  set C : ℝ := (Real.log 4 + 4) + (8 + RHTower.Mertens.mertensTail) with hC
  have hCnn : 0 ≤ C := by
    rw [hC]
    have h1 : (0:ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have h2 : (0:ℝ) ≤ RHTower.Mertens.mertensTail := by
      rw [RHTower.Mertens.mertensTail]
      exact tsum_nonneg fun i => by positivity
    linarith
  -- pass to the interval
  have hsubset := logQuotient_fiber_subset (N := N) (j := j)
  have hnn : ∀ p ∈ Finset.filter Nat.Prime (Finset.Ioc (N / 2 ^ (j + 1)) (N / 2 ^ j)),
      (0:ℝ) ≤ Real.log (p : ℝ) / (p : ℝ) := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_Ioc] at hp
    have hp1 : 1 ≤ p := hp.2.one_lt.le.trans' (by norm_num)
    have hlogp : (0:ℝ) ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hp1)
    positivity
  have hstep : (∑ p ∈ Finset.Icc 1 N with (Nat.Prime p ∧ Nat.log 2 (N / p) = j),
        Real.log (p : ℝ) / (p : ℝ))
      ≤ ∑ p ∈ Finset.Ioc (N / 2 ^ (j + 1)) (N / 2 ^ j) with Nat.Prime p,
          Real.log (p : ℝ) / (p : ℝ) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun p hp _ => hnn p hp)
    intro p hp
    rw [Finset.mem_filter] at hp ⊢
    exact ⟨hsubset (by rw [Finset.mem_filter]; exact hp), hp.2.1⟩
  refine hstep.trans ?_
  rcases Nat.eq_zero_or_pos (N / 2 ^ (j + 1)) with hzero | hpos
  · -- the top block: the interval has no primes
    have htop : N / 2 ^ j ≤ 1 := by
      have h := div_two_pow_le (N := N) (j := j)
      omega
    have hempty : (Finset.Ioc (N / 2 ^ (j + 1)) (N / 2 ^ j)).filter Nat.Prime = ∅ := by
      refine Finset.filter_eq_empty_iff.2 ?_
      intro p hp hprime
      rw [Finset.mem_Ioc] at hp
      have hp2 : 2 ≤ p := hprime.two_le
      omega
    rw [hempty, Finset.sum_empty]
    have hlog3 : (0:ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    linarith
  · -- a generic block: Mertens on the interval, endpoints within a factor 3
    have hle : N / 2 ^ (j + 1) ≤ N / 2 ^ j := by
      have hhalf : N / 2 ^ (j + 1) = N / 2 ^ j / 2 := by
        rw [Nat.div_div_eq_div_mul, ← pow_succ]
      rw [hhalf]
      exact Nat.div_le_self _ 2
    have hmert := sum_Ioc_prime_log_div_le hpos hle
    have hyR : (1:ℝ) ≤ ((N / 2 ^ (j + 1) : ℕ) : ℝ) := by exact_mod_cast hpos
    have hratio : ((N / 2 ^ j : ℕ) : ℝ) ≤ 3 * ((N / 2 ^ (j + 1) : ℕ) : ℝ) := by
      have h := div_two_pow_le (N := N) (j := j)
      have h2 : (N / 2 ^ j : ℕ) ≤ 3 * (N / 2 ^ (j + 1)) := by omega
      exact_mod_cast h2
    have hlogdiff : Real.log ((N / 2 ^ j : ℕ) : ℝ) - Real.log ((N / 2 ^ (j + 1) : ℕ) : ℝ)
        ≤ Real.log 3 := by
      have hypos : (0:ℝ) < ((N / 2 ^ (j + 1) : ℕ) : ℝ) := by linarith
      have hxnat : 0 < N / 2 ^ j := lt_of_lt_of_le hpos hle
      have hxpos : (0:ℝ) < ((N / 2 ^ j : ℕ) : ℝ) := by exact_mod_cast hxnat
      have hlog := Real.log_le_log hxpos hratio
      rw [Real.log_mul (by norm_num) hypos.ne'] at hlog
      linarith
    linarith [hmert, hlogdiff]


/-- **The weighted prime sum with the reciprocal logarithm of the quotient.**  Grouping the primes by
the dyadic size of `⌊N/p⌋` turns the sum into a harmonic sum over the dyadic scales: each scale
contributes `O(1/j)`, and there are `⌊log₂ N⌋` of them. -/
theorem sum_prime_log_div_inv_log_quotient_le (N : ℕ) (hN : 2 ≤ N) :
    (∑ p ∈ Finset.Icc 1 N with (Nat.Prime p ∧ 2 ≤ N / p),
        (Real.log (p : ℝ) / (p : ℝ)) * (1 / Real.log ((N / p : ℕ) : ℝ)))
      ≤ ((Real.log 3 + 2 * ((Real.log 4 + 4) + (8 + RHTower.Mertens.mertensTail))) / Real.log 2)
          * (1 + Real.log ((Nat.log 2 N : ℕ) : ℝ)) := by
  classical
  set C : ℝ := (Real.log 4 + 4) + (8 + RHTower.Mertens.mertensTail) with hC
  set B : ℝ := Real.log 3 + 2 * C with hB
  set J : ℕ := Nat.log 2 N with hJdef
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hCnn : 0 ≤ C := by
    rw [hC]
    have h1 : (0:ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have h2 : (0:ℝ) ≤ RHTower.Mertens.mertensTail := by
      rw [RHTower.Mertens.mertensTail]
      exact tsum_nonneg fun i => by positivity
    linarith
  have hBnn : 0 ≤ B := by
    rw [hB]
    have h3 : (0:ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    linarith
  have hJ1 : 1 ≤ J := by
    rw [hJdef]
    exact Nat.log_pos (by norm_num) hN
  set S : Finset ℕ := {p ∈ Finset.Icc 1 N | Nat.Prime p ∧ 2 ≤ N / p} with hS
  have hmaps : ∀ p ∈ S, Nat.log 2 (N / p) ∈ Finset.Icc 1 J := by
    intro p hp
    rw [hS, Finset.mem_filter, Finset.mem_Icc] at hp
    obtain ⟨⟨hp1, hpN⟩, hprime, hq2⟩ := hp
    rw [Finset.mem_Icc]
    refine ⟨Nat.log_pos (by norm_num) hq2, ?_⟩
    rw [hJdef]
    exact Nat.log_mono_right (Nat.div_le_self N p)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
    (fun p => (Real.log (p : ℝ) / (p : ℝ)) * (1 / Real.log ((N / p : ℕ) : ℝ)))]
  have hfiber : ∀ j ∈ Finset.Icc 1 J,
      (∑ p ∈ S with Nat.log 2 (N / p) = j,
          (Real.log (p : ℝ) / (p : ℝ)) * (1 / Real.log ((N / p : ℕ) : ℝ)))
        ≤ B * (1 / ((j : ℝ) * Real.log 2)) := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    have hj1 : (1:ℝ) ≤ (j : ℝ) := by exact_mod_cast hj.1
    have hjpos : (0:ℝ) < (j : ℝ) * Real.log 2 := by positivity
    -- pointwise: the reciprocal logarithm is at most `1/(j log 2)`
    have hpt : ∀ p ∈ S.filter (fun p => Nat.log 2 (N / p) = j),
        (Real.log (p : ℝ) / (p : ℝ)) * (1 / Real.log ((N / p : ℕ) : ℝ))
          ≤ (Real.log (p : ℝ) / (p : ℝ)) * (1 / ((j : ℝ) * Real.log 2)) := by
      intro p hp
      rw [Finset.mem_filter, hS, Finset.mem_filter, Finset.mem_Icc] at hp
      obtain ⟨⟨⟨hp1, hpN⟩, hprime, hq2⟩, hlogj⟩ := hp
      have hq0 : N / p ≠ 0 := by omega
      have hlow : 2 ^ j ≤ N / p := by
        rw [← hlogj]
        exact Nat.pow_log_le_self 2 hq0
      have hlowR : ((2:ℝ) ^ j) ≤ ((N / p : ℕ) : ℝ) := by
        have : ((2 ^ j : ℕ) : ℝ) ≤ ((N / p : ℕ) : ℝ) := by exact_mod_cast hlow
        simpa using this
      have hqpos : (0:ℝ) < ((N / p : ℕ) : ℝ) := by
        have : 0 < N / p := by omega
        exact_mod_cast this
      have hlogq : (j : ℝ) * Real.log 2 ≤ Real.log ((N / p : ℕ) : ℝ) := by
        have h := Real.log_le_log (by positivity) hlowR
        rwa [Real.log_pow] at h
      have hlogpnn : (0:ℝ) ≤ Real.log (p : ℝ) / (p : ℝ) := by
        have hlogp : (0:ℝ) ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hp1)
        positivity
      refine mul_le_mul_of_nonneg_left ?_ hlogpnn
      exact one_div_le_one_div_of_le hjpos hlogq
    refine le_trans (Finset.sum_le_sum hpt) ?_
    rw [← Finset.sum_mul]
    have hmass : (∑ p ∈ S with Nat.log 2 (N / p) = j, Real.log (p : ℝ) / (p : ℝ)) ≤ B := by
      have hsub : (S.filter fun p => Nat.log 2 (N / p) = j)
          ⊆ {p ∈ Finset.Icc 1 N | Nat.Prime p ∧ Nat.log 2 (N / p) = j} := by
        intro p hp
        rw [Finset.mem_filter, hS, Finset.mem_filter] at hp
        rw [Finset.mem_filter]
        exact ⟨hp.1.1, hp.1.2.1, hp.2⟩
      have hnn : ∀ p ∈ {p ∈ Finset.Icc 1 N | Nat.Prime p ∧ Nat.log 2 (N / p) = j},
          (0:ℝ) ≤ Real.log (p : ℝ) / (p : ℝ) := by
        intro p hp
        rw [Finset.mem_filter, Finset.mem_Icc] at hp
        have hlogp : (0:ℝ) ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hp.1.1)
        positivity
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p hp _ => hnn p hp)) ?_
      rw [hB, hC]
      exact sum_logQuotientFiber_prime_log_div_le N j
    exact mul_le_mul_of_nonneg_right hmass (by positivity)
  refine le_trans (Finset.sum_le_sum hfiber) ?_
  have hval : (∑ j ∈ Finset.Icc 1 J, B * (1 / ((j : ℝ) * Real.log 2)))
      = (B / Real.log 2) * ∑ j ∈ Finset.Icc 1 J, 1 / (j : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    field_simp
  rw [hval]
  refine mul_le_mul_of_nonneg_left (sum_Icc_one_div_le_one_add_log J) (by positivity)

/-- A window of dyadic quotient sizes is an interval of integers. -/
theorem quotient_window_subset {N m n : ℕ} :
    {p ∈ Finset.Icc 1 N | Nat.Prime p ∧ 2 ^ m ≤ N / p ∧ N / p < 2 ^ n}
      ⊆ Finset.Ioc (N / 2 ^ n) (N / 2 ^ m) := by
  intro p hp
  rw [Finset.mem_filter, Finset.mem_Icc] at hp
  obtain ⟨⟨hp1, hpN⟩, _, hlow, hhigh⟩ := hp
  rw [Finset.mem_Ioc]
  refine ⟨?_, (two_pow_le_div_iff hp1).1 hlow⟩
  by_contra hcon
  rw [not_lt] at hcon
  exact absurd ((two_pow_le_div_iff hp1).2 hcon) (not_le.mpr hhigh)

/-- The two endpoints of a dyadic quotient window are within a factor `2^{n-m}`, and one unit. -/
theorem div_two_pow_le_window {N m n : ℕ} (hmn : m ≤ n) :
    N / 2 ^ m ≤ 2 ^ (n - m) * (N / 2 ^ n) + 2 ^ (n - m) := by
  have hsplit : N / 2 ^ n = N / 2 ^ m / 2 ^ (n - m) := by
    rw [Nat.div_div_eq_div_mul, ← pow_add]
    congr 2
    omega
  rw [hsplit]
  have hpos : 0 < 2 ^ (n - m) := by positivity
  have h1 := Nat.div_add_mod (N / 2 ^ m) (2 ^ (n - m))
  have h2 := Nat.mod_lt (N / 2 ^ m) hpos
  omega


/-- **The Mertens mass of a dyadic quotient window.**  A window `2^m ≤ ⌊N/p⌋ < 2^n` of primes carries
mass `(n - m)·log 2 + O(1)`: the geometric blocking of the prime range in the dyadic scale of the
quotient. -/
theorem sum_quotient_window_prime_log_div_le (N m n : ℕ) (hmn : m ≤ n) :
    (∑ p ∈ Finset.Icc 1 N with (Nat.Prime p ∧ 2 ^ m ≤ N / p ∧ N / p < 2 ^ n),
        Real.log (p : ℝ) / (p : ℝ))
      ≤ ((n : ℝ) - (m : ℝ) + 1) * Real.log 2
        + 2 * ((Real.log 4 + 4) + (8 + RHTower.Mertens.mertensTail)) := by
  classical
  set C : ℝ := (Real.log 4 + 4) + (8 + RHTower.Mertens.mertensTail) with hC
  have hCnn : 0 ≤ C := by
    rw [hC]
    have h1 : (0:ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have h2 : (0:ℝ) ≤ RHTower.Mertens.mertensTail := by
      rw [RHTower.Mertens.mertensTail]
      exact tsum_nonneg fun i => by positivity
    linarith
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hnm : ((n - m : ℕ) : ℝ) = (n : ℝ) - (m : ℝ) := by
    rw [Nat.cast_sub hmn]
  have hnn : ∀ p ∈ Finset.filter Nat.Prime (Finset.Ioc (N / 2 ^ n) (N / 2 ^ m)),
      (0:ℝ) ≤ Real.log (p : ℝ) / (p : ℝ) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    have hp1 : 1 ≤ p := hp.2.one_lt.le.trans' (by norm_num)
    have hlogp : (0:ℝ) ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hp1)
    positivity
  have hstep : (∑ p ∈ Finset.Icc 1 N with (Nat.Prime p ∧ 2 ^ m ≤ N / p ∧ N / p < 2 ^ n),
        Real.log (p : ℝ) / (p : ℝ))
      ≤ ∑ p ∈ Finset.Ioc (N / 2 ^ n) (N / 2 ^ m) with Nat.Prime p,
          Real.log (p : ℝ) / (p : ℝ) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun p hp _ => hnn p hp)
    intro p hp
    rw [Finset.mem_filter] at hp ⊢
    exact ⟨quotient_window_subset (by rw [Finset.mem_filter]; exact hp), hp.2.1⟩
  refine hstep.trans ?_
  rcases Nat.eq_zero_or_pos (N / 2 ^ n) with hzero | hpos
  · -- the top window: bound by all primes up to the upper endpoint
    rcases Nat.eq_zero_or_pos (N / 2 ^ m) with hzero' | hpos'
    · have hempty : Finset.Ioc (N / 2 ^ n) (N / 2 ^ m) = ∅ := by
        rw [hzero, hzero']
        simp
      rw [hempty]
      simp only [Finset.filter_empty, Finset.sum_empty]
      have hnmnn : (0:ℝ) ≤ (n : ℝ) - (m : ℝ) := by
        rw [← hnm]
        positivity
      nlinarith [hCnn, hlog2, hnmnn]
    · have hIcc : Finset.Ioc (N / 2 ^ n) (N / 2 ^ m) = Finset.Icc 1 (N / 2 ^ m) := by
        rw [hzero]
        ext a
        simp only [Finset.mem_Ioc, Finset.mem_Icc]
        omega
      rw [hIcc]
      have hmert := RHTower.Mertens.mertens_first_prime (N / 2 ^ m) hpos'
      rw [abs_le] at hmert
      have hsmall : N / 2 ^ m < 2 ^ (n - m) := by
        have hNlt : N < 2 ^ n := by
          by_contra hcon
          rw [not_lt] at hcon
          have : 1 ≤ N / 2 ^ n := (Nat.one_le_div_iff (by positivity)).2 hcon
          omega
        have hpow : (2 : ℕ) ^ n = 2 ^ m * 2 ^ (n - m) := by
          rw [← pow_add]
          congr 1
          omega
        by_contra hcon
        rw [not_lt] at hcon
        have hge : 2 ^ m * 2 ^ (n - m) ≤ N := by
          calc 2 ^ m * 2 ^ (n - m) ≤ 2 ^ m * (N / 2 ^ m) :=
                Nat.mul_le_mul_left _ hcon
            _ = (N / 2 ^ m) * 2 ^ m := by ring
            _ ≤ N := Nat.div_mul_le_self N (2 ^ m)
        rw [← hpow] at hge
        omega
      have hlogsmall : Real.log ((N / 2 ^ m : ℕ) : ℝ) ≤ ((n : ℝ) - (m : ℝ)) * Real.log 2 := by
        have hle : ((N / 2 ^ m : ℕ) : ℝ) ≤ ((2 ^ (n - m) : ℕ) : ℝ) := by
          have : (N / 2 ^ m : ℕ) ≤ 2 ^ (n - m) := le_of_lt hsmall
          exact_mod_cast this
        have hlog := Real.log_le_log (by exact_mod_cast hpos') hle
        rw [Nat.cast_pow, Real.log_pow, hnm] at hlog
        exact hlog
      linarith [hmert.2, hlogsmall]
  · -- a generic window: Mertens on the interval, endpoints within `2^{n-m+1}`
    have hle : N / 2 ^ n ≤ N / 2 ^ m := by
      have hsplit : N / 2 ^ n = N / 2 ^ m / 2 ^ (n - m) := by
        rw [Nat.div_div_eq_div_mul, ← pow_add]
        congr 2
        omega
      rw [hsplit]
      exact Nat.div_le_self _ _
    have hmert := sum_Ioc_prime_log_div_le hpos hle
    have hnat : N / 2 ^ m ≤ 2 ^ (n - m + 1) * (N / 2 ^ n) := by
      have hwin := div_two_pow_le_window (N := N) (m := m) (n := n) hmn
      have h1 : 1 ≤ N / 2 ^ n := hpos
      have hpow : (2 : ℕ) ^ (n - m + 1) = 2 ^ (n - m) * 2 := by
        rw [pow_succ]
      rw [hpow]
      nlinarith [hwin, h1]
    have hlogdiff : Real.log ((N / 2 ^ m : ℕ) : ℝ) - Real.log ((N / 2 ^ n : ℕ) : ℝ)
        ≤ ((n : ℝ) - (m : ℝ) + 1) * Real.log 2 := by
      have hypos : (0:ℝ) < ((N / 2 ^ n : ℕ) : ℝ) := by exact_mod_cast hpos
      have hxnat : 0 < N / 2 ^ m := lt_of_lt_of_le hpos hle
      have hxpos : (0:ℝ) < ((N / 2 ^ m : ℕ) : ℝ) := by exact_mod_cast hxnat
      have hcast : ((N / 2 ^ m : ℕ) : ℝ)
          ≤ ((2 : ℝ) ^ (n - m + 1)) * ((N / 2 ^ n : ℕ) : ℝ) := by
        have h : ((N / 2 ^ m : ℕ) : ℝ) ≤ ((2 ^ (n - m + 1) * (N / 2 ^ n) : ℕ) : ℝ) := by
          exact_mod_cast hnat
        rwa [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at h
      have hlog := Real.log_le_log hxpos hcast
      rw [Real.log_mul (by positivity) hypos.ne', Real.log_pow] at hlog
      have hexp : ((n - m + 1 : ℕ) : ℝ) = (n : ℝ) - (m : ℝ) + 1 := by
        push_cast [hnm]
        ring
      rw [hexp] at hlog
      linarith
    linarith [hmert, hlogdiff]

end RHTower.Sieve
end
