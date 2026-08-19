import GaloisForLFunctions.RHTower.Sieve.PrimeCosineTailAbel

/-!
# The tail cosine sum against the Route-T envelope

`Sieve/PrimeCosineTailAbel` reduces the Granville–Soundararajan tail to a uniform *linear* bound on
the twisted prime polynomials of the initial ranges `(y, i]`, `i ≤ z`.  Here that hypothesis is
matched against the corpus's Route-T bound
`Sieve/PrimeBlockTwistBound.exists_norm_primeBlockPoly_routeT_le`, leaving only the size comparison
between the envelope and the block top — an inequality between named quantities, with no remaining
arithmetic content.

The two partial-summation weights are bounded once and for all: `1/log 2 + 1/log(n+1) ≤ 3` for
`n ≥ 1`.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

theorem inv_log_two_add_inv_log_succ_le_three {n : ℕ} (hn : 1 ≤ n) :
    1 / Real.log 2 + 1 / Real.log ((n + 1 : ℕ) : ℝ) ≤ 3 := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlow : Real.log 2 ≤ Real.log ((n + 1 : ℕ) : ℝ) := by
    refine Real.log_le_log (by norm_num) ?_
    have : (2 : ℕ) ≤ n + 1 := by omega
    exact_mod_cast this
  have hinv : 1 / Real.log ((n + 1 : ℕ) : ℝ) ≤ 1 / Real.log 2 :=
    one_div_le_one_div_of_le hlog2 hlow
  have hval : 1 / Real.log 2 ≤ 3 / 2 := by
    rw [div_le_div_iff₀ hlog2 (by norm_num)]
    have h2 : (2 : ℝ) / 3 ≤ Real.log 2 := by
      have := Real.log_two_gt_d9
      norm_num at this ⊢
      linarith
    linarith
  linarith

/-- **The prime polynomial of an initial range against the Route-T envelope.** -/
theorem exists_norm_primeBlockPoly_primesRange_le :
    ∃ A delta C : ℝ, 0 < delta ∧ 0 < C ∧
      ∀ (y i : ℕ) (t : ℝ), 1 ≤ y → y ≤ i →
        ‖primeBlockPoly (primesRange y i) (t / (2 * Real.pi))‖
          ≤ 3 * (routeTTwistEnvelope A delta C (-t) (max (i : ℝ) 1)
              + routeTTwistEnvelope A delta C (-t) (max (y : ℝ) 1) + 14 * Real.exp 9) := by
  obtain ⟨A, delta, C, hdelta, hC, hbound⟩ := exists_norm_primeBlockPoly_routeT_le
  refine ⟨A, delta, C, hdelta, hC, ?_⟩
  intro y i t hy hyi
  have hw : -(2 * Real.pi * (t / (2 * Real.pi))) = -t := by
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp
  have hmem : ∀ p, p ∈ primesRange y i ↔ (p.Prime ∧ y < p ∧ p ≤ i) := fun p => mem_primesRange
  have hb := hbound (primesRange y i) y i hyi hmem (t / (2 * Real.pi))
  rw [hw] at hb
  refine hb.trans ?_
  have hi1 : 1 ≤ i := le_trans hy hyi
  have hEi : (0 : ℝ) ≤ routeTTwistEnvelope A delta C (-t) (max (i : ℝ) 1) :=
    routeTTwistEnvelope_nonneg hC.le (le_max_right _ _)
  have hEy : (0 : ℝ) ≤ routeTTwistEnvelope A delta C (-t) (max (y : ℝ) 1) :=
    routeTTwistEnvelope_nonneg hC.le (le_max_right _ _)
  have he9 : (0 : ℝ) ≤ 7 * Real.exp 9 := by positivity
  have hwi := inv_log_two_add_inv_log_succ_le_three hi1
  have hwy := inv_log_two_add_inv_log_succ_le_three hy
  have hpi : (0 : ℝ) ≤ 1 / Real.log 2 + 1 / Real.log ((i + 1 : ℕ) : ℝ) := by
    have h1 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have h2 : (0 : ℝ) ≤ Real.log ((i + 1 : ℕ) : ℝ) :=
      Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (by omega))
    positivity
  have hpy : (0 : ℝ) ≤ 1 / Real.log 2 + 1 / Real.log ((y + 1 : ℕ) : ℝ) := by
    have h1 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have h2 : (0 : ℝ) ≤ Real.log ((y + 1 : ℕ) : ℝ) :=
      Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (by omega))
    positivity
  nlinarith [hEi, hEy, he9, hwi, hwy, hpi, hpy]

/-- **The Granville–Soundararajan tail against the Route-T envelope.**  Everything arithmetic is
discharged; the hypothesis is a pure size comparison between the envelope and the block top. -/
theorem exists_abs_sum_cos_div_primesRange_le_routeT :
    ∃ A delta C : ℝ, 0 < delta ∧ 0 < C ∧
      ∀ (y z : ℕ) (t ρ : ℝ), 1 ≤ y → 0 < z → 0 ≤ ρ →
        (∀ i, y ≤ i → i ≤ z →
          3 * (routeTTwistEnvelope A delta C (-t) (max (i : ℝ) 1)
              + routeTTwistEnvelope A delta C (-t) (max (y : ℝ) 1) + 14 * Real.exp 9)
            ≤ ρ * (i : ℝ)) →
        |∑ p ∈ primesRange y z, Real.cos (t * Real.log (p : ℝ)) / (p : ℝ)|
          ≤ ρ * (2 + Real.log (z : ℝ)) := by
  obtain ⟨A, delta, C, hdelta, hC, hbound⟩ := exists_norm_primeBlockPoly_primesRange_le
  refine ⟨A, delta, C, hdelta, hC, ?_⟩
  intro y z t ρ hy hz hρ hsize
  refine abs_sum_cos_div_primesRange_le_of_norm hz hρ ?_
  intro i hi
  rcases le_or_gt y i with hyi | hiy
  · exact le_trans (hbound y i t hy hyi) (hsize i hyi hi)
  · have hempty : primesRange y i = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro p hp
      rw [mem_primesRange] at hp
      omega
    rw [hempty, primeBlockPoly, Finset.sum_empty, norm_zero]
    positivity

end

end RHTower.Sieve
