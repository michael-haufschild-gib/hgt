import GaloisForLFunctions.RHTower.Sieve.VonMangoldtTwistPrimeSum
import GaloisForLFunctions.HTGeometry.DiscreteAbelRing

/-!
# From the twisted Chebyshev sum to the twisted prime-counting sum

Matomäki--Radziwiłł consume the prime-indicator twist `∑_{p ≤ K} p^{-iτ}`, while the contour
estimate produces the log-weighted twist `∑_{p ≤ K} (log p) p^{-iτ}`.  Discrete summation by parts
against `1/log` converts one into the other: the weight `1/log` is positive and decreasing past `2`,
so the transform costs only the boundary term at `K` plus the total variation of `1/log`, both
weighted by whatever majorant the contour estimate supplies for the partial sums.
-/

namespace RHTower.Sieve

open Complex ArithmeticFunction

/-- The prime-indicator twist `p ↦ p^{-iτ}`. -/
noncomputable def primeTwist (τ : ℝ) (n : ℕ) : ℂ :=
  if n.Prime then (n : ℂ) ^ (-((τ : ℂ) * Complex.I)) else 0

@[simp] theorem primeTwist_zero' (τ : ℝ) : primeTwist τ 0 = 0 := by
  rw [primeTwist, if_neg Nat.not_prime_zero]

@[simp] theorem vonMangoldtPrimeTwist_zero' (τ : ℝ) : vonMangoldtPrimeTwist τ 0 = 0 := by
  rw [vonMangoldtPrimeTwist, if_neg Nat.not_prime_zero]

theorem vonMangoldtPrimeTwist_one' (τ : ℝ) : vonMangoldtPrimeTwist τ 1 = 0 := by
  rw [vonMangoldtPrimeTwist, if_neg Nat.not_prime_one]

/-- The log weight is exactly the ratio of the two twists. -/
theorem vonMangoldtPrimeTwist_mul_invLog (τ : ℝ) (n : ℕ) :
    vonMangoldtPrimeTwist τ n * ((1 / Real.log (n : ℝ) : ℝ) : ℂ) = primeTwist τ n := by
  unfold vonMangoldtPrimeTwist primeTwist
  by_cases hp : n.Prime
  · rw [if_pos hp, if_pos hp]
    have hn : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hp.one_lt
    have hlog : Real.log (n : ℝ) ≠ 0 := ne_of_gt (Real.log_pos hn)
    have hlogC : ((Real.log (n : ℝ) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hlog
    rw [one_div, Complex.ofReal_inv]
    field_simp
  · rw [if_neg hp, if_neg hp]
    ring

theorem sum_range_succ_eq_sum_Icc {f : ℕ → ℂ} (h0 : f 0 = 0) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), f n = ∑ n ∈ Finset.Icc 1 N, f n := by
  classical
  have hset : Finset.range (N + 1) = insert 0 (Finset.Icc 1 N) := by
    ext k
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc, Nat.lt_succ_iff]
    omega
  rw [hset, Finset.sum_insert (by simp), h0, zero_add]

/-- **Summation by parts against `1/log`.** -/
theorem sum_primeTwist_eq_abel (τ : ℝ) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, primeTwist τ n
      = (∑ m ∈ Finset.Icc 1 N,
          (∑ k ∈ Finset.Icc 1 m, vonMangoldtPrimeTwist τ k) *
            (((1 / Real.log (m : ℝ) : ℝ) : ℂ) - ((1 / Real.log ((m + 1 : ℕ) : ℝ) : ℝ) : ℂ)))
        + (∑ k ∈ Finset.Icc 1 N, vonMangoldtPrimeTwist τ k) *
            ((1 / Real.log ((N + 1 : ℕ) : ℝ) : ℝ) : ℂ) := by
  have hpt : ∀ n ∈ Finset.Icc 1 N, primeTwist τ n
      = vonMangoldtPrimeTwist τ n * ((1 / Real.log (n : ℝ) : ℝ) : ℂ) :=
    fun n _ => (vonMangoldtPrimeTwist_mul_invLog τ n).symm
  rw [Finset.sum_congr rfl hpt]
  exact HTGeometry.sum_mul_eq_partial_mul_diff_ring
    (fun n => vonMangoldtPrimeTwist τ n)
    (fun n => ((1 / Real.log (n : ℝ) : ℝ) : ℂ)) N

theorem invLog_antitone {m : ℕ} (hm : 2 ≤ m) :
    1 / Real.log ((m + 1 : ℕ) : ℝ) ≤ 1 / Real.log (m : ℝ) := by
  have hm1 : (1 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hlogm : 0 < Real.log (m : ℝ) := Real.log_pos hm1
  have hcast : (((m + 1 : ℕ) : ℝ)) = (m : ℝ) + 1 := by push_cast; ring
  rw [hcast]
  exact one_div_le_one_div_of_le hlogm
    (Real.log_le_log (by linarith) (by linarith))

/-- **The twisted prime-counting sum from the twisted Chebyshev sum.**  Any majorant for the partial
sums of the log-weighted twist transfers, by summation by parts, to the prime-indicator twist. -/
theorem norm_sum_primeTwist_le_of_partialSum_bound (τ : ℝ) (N : ℕ) (E : ℕ → ℝ)
    (hE : ∀ m, m ≤ N → ‖∑ k ∈ Finset.range (m + 1), vonMangoldtPrimeTwist τ k‖ ≤ E m) :
    ‖∑ n ∈ Finset.range (N + 1), primeTwist τ n‖
      ≤ (∑ m ∈ Finset.Icc 2 N,
            E m * (1 / Real.log (m : ℝ) - 1 / Real.log ((m + 1 : ℕ) : ℝ)))
        + E N / Real.log ((N + 1 : ℕ) : ℝ) := by
  classical
  have hAnorm : ∀ m, m ≤ N →
      ‖∑ k ∈ Finset.Icc 1 m, vonMangoldtPrimeTwist τ k‖ ≤ E m := by
    intro m hm
    rw [← sum_range_succ_eq_sum_Icc (vonMangoldtPrimeTwist_zero' τ) m]
    exact hE m hm
  have hshrink : (∑ m ∈ Finset.Icc 2 N,
        (∑ k ∈ Finset.Icc 1 m, vonMangoldtPrimeTwist τ k) *
          (((1 / Real.log (m : ℝ) : ℝ) : ℂ) - ((1 / Real.log ((m + 1 : ℕ) : ℝ) : ℝ) : ℂ)))
      = ∑ m ∈ Finset.Icc 1 N,
          (∑ k ∈ Finset.Icc 1 m, vonMangoldtPrimeTwist τ k) *
            (((1 / Real.log (m : ℝ) : ℝ) : ℂ)
              - ((1 / Real.log ((m + 1 : ℕ) : ℝ) : ℝ) : ℂ)) := by
    refine Finset.sum_subset ?_ ?_
    · intro x hx
      simp only [Finset.mem_Icc] at hx ⊢
      exact ⟨by omega, hx.2⟩
    · intro x hx hnx
      simp only [Finset.mem_Icc] at hx hnx
      have hx1 : x = 1 := by omega
      subst hx1
      have hzero : (∑ k ∈ Finset.Icc 1 1, vonMangoldtPrimeTwist τ k) = 0 := by
        rw [Finset.Icc_self, Finset.sum_singleton, vonMangoldtPrimeTwist_one']
      rw [hzero, zero_mul]
  rw [sum_range_succ_eq_sum_Icc (primeTwist_zero' τ) N, sum_primeTwist_eq_abel τ N, ← hshrink]
  refine le_trans (norm_add_le _ _) (add_le_add ?_ ?_)
  · refine le_trans (norm_sum_le _ _) ?_
    refine Finset.sum_le_sum fun m hm => ?_
    simp only [Finset.mem_Icc] at hm
    have hdiff : 0 ≤ 1 / Real.log (m : ℝ) - 1 / Real.log ((m + 1 : ℕ) : ℝ) := by
      have := invLog_antitone hm.1
      linarith
    rw [norm_mul]
    have hnorm2 : ‖(((1 / Real.log (m : ℝ) : ℝ) : ℂ)
        - ((1 / Real.log ((m + 1 : ℕ) : ℝ) : ℝ) : ℂ))‖
        = 1 / Real.log (m : ℝ) - 1 / Real.log ((m + 1 : ℕ) : ℝ) := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hdiff]
    rw [hnorm2]
    exact mul_le_mul_of_nonneg_right (hAnorm m hm.2) hdiff
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hlog0 : 0 ≤ 1 / Real.log ((N + 1 : ℕ) : ℝ) := by
      rcases Nat.eq_zero_or_pos N with rfl | hN
      · norm_num
      · have hcast : (((N + 1 : ℕ) : ℝ)) = (N : ℝ) + 1 := by push_cast; ring
        rw [hcast]
        have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
        have : 0 ≤ Real.log ((N : ℝ) + 1) := Real.log_nonneg (by linarith)
        positivity
    rw [abs_of_nonneg hlog0]
    have hfin := mul_le_mul_of_nonneg_right (hAnorm N le_rfl) hlog0
    calc ‖∑ k ∈ Finset.Icc 1 N, vonMangoldtPrimeTwist τ k‖
          * (1 / Real.log ((N + 1 : ℕ) : ℝ))
        ≤ E N * (1 / Real.log ((N + 1 : ℕ) : ℝ)) := hfin
      _ = E N / Real.log ((N + 1 : ℕ) : ℝ) := by rw [mul_one_div]

/-- The total variation of `1/log` past `2` is at most `1/log 2`. -/
theorem sum_Icc_invLog_diff_le (N : ℕ) :
    ∑ m ∈ Finset.Icc 2 N, (1 / Real.log (m : ℝ) - 1 / Real.log ((m + 1 : ℕ) : ℝ))
      ≤ 1 / Real.log 2 := by
  classical
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  rcases Nat.lt_or_ge N 2 with hN | hN
  · have hempty : Finset.Icc 2 N = ∅ := by
      rw [Finset.Icc_eq_empty]
      omega
    rw [hempty, Finset.sum_empty]
    positivity
  · have hIcc : Finset.Icc 2 N = Finset.Ico 2 (N + 1) := (Finset.Ico_add_one_right_eq_Icc 2 N).symm
    rw [hIcc, Finset.sum_Ico_eq_sum_range]
    have hcongr : ∀ i ∈ Finset.range (N + 1 - 2),
        1 / Real.log (((2 + i : ℕ)) : ℝ) - 1 / Real.log (((2 + i + 1 : ℕ)) : ℝ)
          = (fun j : ℕ => 1 / Real.log ((2 + j : ℕ) : ℝ)) i
            - (fun j : ℕ => 1 / Real.log ((2 + j : ℕ) : ℝ)) (i + 1) := by
      intro i _
      simp only []
      congr 3
    rw [Finset.sum_congr rfl hcongr,
      Finset.sum_range_sub' (fun j : ℕ => 1 / Real.log ((2 + j : ℕ) : ℝ)) (N + 1 - 2)]
    have hidx : ((2 + (N + 1 - 2) : ℕ)) = N + 1 := by omega
    rw [hidx]
    have hpos : 0 ≤ 1 / Real.log ((N + 1 : ℕ) : ℝ) := by
      have hcast : (((N + 1 : ℕ) : ℝ)) = (N : ℝ) + 1 := by push_cast; ring
      rw [hcast]
      have hN1 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      have : 0 ≤ Real.log ((N : ℝ) + 1) := Real.log_nonneg (by linarith)
      positivity
    have hzero : ((2 + 0 : ℕ) : ℝ) = (2 : ℝ) := by norm_num
    rw [hzero]
    linarith

/-- **Lemma 2.3, prime form, from the Chebyshev form.**  A monotone majorant for the log-weighted
twisted partial sums bounds the prime-indicator twist by the same order. -/
theorem norm_sum_primeTwist_le_of_monotone_bound (τ : ℝ) (N : ℕ) (E : ℕ → ℝ)
    (hE : ∀ m, m ≤ N → ‖∑ k ∈ Finset.range (m + 1), vonMangoldtPrimeTwist τ k‖ ≤ E m)
    (hmono : ∀ m, m ≤ N → E m ≤ E N) :
    ‖∑ n ∈ Finset.range (N + 1), primeTwist τ n‖
      ≤ E N * (1 / Real.log 2 + 1 / Real.log ((N + 1 : ℕ) : ℝ)) := by
  have hEN : 0 ≤ E N := le_trans (norm_nonneg _) (hE N le_rfl)
  refine le_trans (norm_sum_primeTwist_le_of_partialSum_bound τ N E hE) ?_
  have hstep : (∑ m ∈ Finset.Icc 2 N,
        E m * (1 / Real.log (m : ℝ) - 1 / Real.log ((m + 1 : ℕ) : ℝ)))
      ≤ E N * (1 / Real.log 2) := by
    have hterm : ∀ m ∈ Finset.Icc 2 N,
        E m * (1 / Real.log (m : ℝ) - 1 / Real.log ((m + 1 : ℕ) : ℝ))
          ≤ E N * (1 / Real.log (m : ℝ) - 1 / Real.log ((m + 1 : ℕ) : ℝ)) := by
      intro m hm
      simp only [Finset.mem_Icc] at hm
      have hdiff : 0 ≤ 1 / Real.log (m : ℝ) - 1 / Real.log ((m + 1 : ℕ) : ℝ) := by
        have := invLog_antitone hm.1
        linarith
      exact mul_le_mul_of_nonneg_right (hmono m hm.2) hdiff
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_Icc_invLog_diff_le N) hEN
  have hbnd : E N / Real.log ((N + 1 : ℕ) : ℝ)
      = E N * (1 / Real.log ((N + 1 : ℕ) : ℝ)) := by rw [mul_one_div]
  rw [hbnd, mul_add]
  exact add_le_add hstep le_rfl

end RHTower.Sieve
