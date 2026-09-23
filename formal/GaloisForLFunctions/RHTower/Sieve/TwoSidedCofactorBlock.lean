import GaloisForLFunctions.RHTower.Sieve.LadderErrorBudget

/-!
# The cofactor block of a thin prime range, over a dyadic block of indices

The fibres of the Route E reduction do not live on an initial segment but on a dyadic block
`[A₀, B₀]` of ratio at most four, so the cofactor range of a thin prime range is two-sided.  Its
discrepancy against the individual cofactor sets is the same as in the one-sided case: the two
moving endpoints contribute proportionally to the relative width `η`, and the multiples of the prime
contribute `B₀/Q²`.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- The common cofactor block of the `j`-th step, over a two-sided range of indices. -/
def geomCofactorBlockAt (A₀ B₀ : ℕ) (Q η : ℝ) (j : ℕ) : Finset ℕ :=
  Finset.Icc ⌈(A₀ : ℝ) / ((Q * (1 + η) ^ j) * (1 + η))⌉₊ ⌊(B₀ : ℝ) / (Q * (1 + η) ^ j)⌋₊

theorem geomCofactorBlockAt_one (M : ℕ) (Q η : ℝ) (j : ℕ) :
    geomCofactorBlockAt 1 M Q η j = geomCofactorBlock M Q η j := rfl

/-- The gap set of one `(step, prime)` pair over a two-sided range. -/
def ladderGapSetAt (A₀ B₀ : ℕ) (Q η : ℝ) (x : (_ : ℕ) × ℕ) : Finset ℕ :=
  geomCofactorBlockAt A₀ B₀ Q η x.1 \ {m ∈ ramareCofactorSet (Finset.Icc A₀ B₀) x.2 | ¬ x.2 ∣ m}

/-- **The two-sided gap of one step.**  The cost is the two moving endpoints plus the multiples of
the prime, exactly as in the one-sided case. -/
theorem card_ladderGapSetAt_le {P : Finset ℕ} (A₀ B₀ : ℕ) {Q η : ℝ} (hQ : 0 < Q) (hη : 0 ≤ η)
    {L : ℕ} {x : (_ : ℕ) × ℕ} (hx : x ∈ ladderIndex P Q η L)
    (hPprime : ∀ q ∈ P, q.Prime) :
    ((ladderGapSetAt A₀ B₀ Q η x).card : ℝ)
      ≤ ((A₀ : ℝ) + (B₀ : ℝ)) * η / (Q * (1 + η) ^ x.1) + 4
        + ((B₀ : ℝ) / (Q * (1 + η) ^ x.1) ^ (2 : ℕ) + 1) := by
  classical
  set Qj : ℝ := Q * (1 + η) ^ x.1 with hQj
  have hr1 : (1 : ℝ) ≤ 1 + η := by linarith
  have hQj0 : (0 : ℝ) < Qj := by
    rw [hQj]
    have : (0 : ℝ) < (1 + η) ^ x.1 := by positivity
    positivity
  rw [ladderIndex, Finset.mem_sigma] at hx
  have hp := hPprime x.2 (geomBlock_subset P Q (1 + η) x.1 hx.2)
  have hmem := hx.2
  rw [geomBlock, Finset.mem_filter] at hmem
  obtain ⟨-, hlo, hhi⟩ := hmem
  have hpow : Q * (1 + η) ^ (x.1 + 1) = Qj * (1 + η) := by
    rw [hQj, pow_succ]
    ring
  rw [hpow] at hhi
  rw [← hQj] at hlo
  have hbase := card_cofactor_symmDiff_le (A₀ := A₀) (B₀ := B₀) hQj0 hη hp.pos hlo hhi
  rw [ladderGapSetAt, geomCofactorBlockAt, ← hQj]
  exact hbase

/-- **The two-sided ladder gap budget.** -/
theorem sum_card_ladderGapSetAt_le {P : Finset ℕ} (A₀ B₀ : ℕ) {Q η : ℝ} (hQ : 0 < Q) (hη : 0 ≤ η)
    (L : ℕ) (hPprime : ∀ q ∈ P, q.Prime) :
    (∑ x ∈ ladderIndex P Q η L, ((ladderGapSetAt A₀ B₀ Q η x).card : ℝ))
      ≤ ∑ j ∈ Finset.range L, (Q * (1 + η) ^ j * η + 1)
          * (((A₀ : ℝ) + (B₀ : ℝ)) * η / (Q * (1 + η) ^ j) + 5
            + (B₀ : ℝ) / (Q * (1 + η) ^ j) ^ (2 : ℕ)) := by
  classical
  have hstep : ∀ x ∈ ladderIndex P Q η L, ((ladderGapSetAt A₀ B₀ Q η x).card : ℝ)
      ≤ ((A₀ : ℝ) + (B₀ : ℝ)) * η / (Q * (1 + η) ^ x.1) + 5
        + (B₀ : ℝ) / (Q * (1 + η) ^ x.1) ^ (2 : ℕ) := by
    intro x hx
    have h := card_ladderGapSetAt_le A₀ B₀ hQ hη hx hPprime
    linarith
  refine (Finset.sum_le_sum hstep).trans ?_
  have hflat : (∑ x ∈ ladderIndex P Q η L,
      (((A₀ : ℝ) + (B₀ : ℝ)) * η / (Q * (1 + η) ^ x.1) + 5
        + (B₀ : ℝ) / (Q * (1 + η) ^ x.1) ^ (2 : ℕ)))
      = ∑ j ∈ Finset.range L, ((geomBlock P Q (1 + η) j).card : ℝ)
          * (((A₀ : ℝ) + (B₀ : ℝ)) * η / (Q * (1 + η) ^ j) + 5
            + (B₀ : ℝ) / (Q * (1 + η) ^ j) ^ (2 : ℕ)) := by
    rw [ladderIndex, Finset.sum_sigma]
    refine Finset.sum_congr rfl fun j _ => ?_
    show (∑ _p ∈ geomBlock P Q (1 + η) j,
        (((A₀ : ℝ) + (B₀ : ℝ)) * η / (Q * (1 + η) ^ j) + 5
          + (B₀ : ℝ) / (Q * (1 + η) ^ j) ^ (2 : ℕ))) = _
    rw [Finset.sum_const, nsmul_eq_mul]
  rw [hflat]
  refine Finset.sum_le_sum fun j _ => ?_
  have hQj0 : (0 : ℝ) < Q * (1 + η) ^ j := by
    have : (0 : ℝ) < (1 + η) ^ j := by positivity
    positivity
  have hfac : (0 : ℝ) ≤ ((A₀ : ℝ) + (B₀ : ℝ)) * η / (Q * (1 + η) ^ j) + 5
      + (B₀ : ℝ) / (Q * (1 + η) ^ j) ^ (2 : ℕ) := by
    have h1 : (0 : ℝ) ≤ ((A₀ : ℝ) + (B₀ : ℝ)) * η / (Q * (1 + η) ^ j) := by positivity
    have h2 : (0 : ℝ) ≤ (B₀ : ℝ) / (Q * (1 + η) ^ j) ^ (2 : ℕ) := by positivity
    linarith
  exact mul_le_mul_of_nonneg_right (card_geomBlock_le P hQ hη j) hfac

end

end RHTower.Sieve
