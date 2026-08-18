import GaloisForLFunctions.RHTower.Sieve.RamareBlockSplit
import GaloisForLFunctions.RHTower.RouteEForbiddenSupportStability

/-!
# The budget of the ladder error

The mean square of the Ramaré ladder error is the product of a mean-value factor, an overlap count
`K`, and the total size of the gap sets.  Both of the last two are now explicit:

* the overlap count is the number of designated primes dividing an index, and designated primes
  exceed `Q`, so their product bounds the index — at most `log N / log Q` of them;
* each gap set is a cofactor set against the common block of its step, whose size is the moving
  endpoints (relative width `η`) plus the multiples of the prime;
* each step of the ladder holds the primes of an interval of relative width `η`, so it has at most
  `Q_j η + 1` members.

Together these turn the ladder error into a closed expression in `M`, `Q`, `η` and `L`.
-/

namespace RHTower.Sieve

open MeasureTheory Finset

noncomputable section

/-! ## The overlap count -/

/-- **Designated primes dividing a bounded index are few.**  Distinct primes above `Q` whose
product divides `n ≤ N` number at most `log N / log Q`. -/
theorem card_designatedPrimes_dvd_le {P : Finset ℕ} {Q : ℝ} (hQ : 1 < Q)
    (hPprime : ∀ p ∈ P, p.Prime) (hPge : ∀ p ∈ P, Q ≤ (p : ℝ))
    {N n : ℕ} (hn : 1 ≤ n) (hnN : n ≤ N) :
    ((P.filter (fun p => p ∣ n)).card : ℝ) ≤ Real.log N / Real.log Q := by
  classical
  have hn0 : n ≠ 0 := by omega
  have hsub : P.filter (fun p => p ∣ n) ⊆ n.primeFactors := by
    intro p hp
    rw [Finset.mem_filter] at hp
    exact Nat.mem_primeFactors.2 ⟨hPprime p hp.1, hp.2, hn0⟩
  have hge : ∀ p ∈ P.filter (fun p => p ∣ n), Q ≤ (p : ℝ) := fun p hp =>
    hPge p (Finset.mem_filter.1 hp).1
  refine (ForbiddenSupport.card_le_log_div_log hn0 hsub hQ hge).trans ?_
  have hlogQ : 0 < Real.log Q := Real.log_pos hQ
  have hlog : Real.log n ≤ Real.log N :=
    Real.log_le_log (by exact_mod_cast hn) (by exact_mod_cast hnN)
  gcongr

/-! ## The size of one ladder step -/

/-- **A ladder step holds the primes of an interval of relative width `η`.** -/
theorem card_geomBlock_le (P : Finset ℕ) {Q η : ℝ} (hQ : 0 < Q) (hη : 0 ≤ η) (j : ℕ) :
    ((geomBlock P Q (1 + η) j).card : ℝ) ≤ Q * (1 + η) ^ j * η + 1 := by
  classical
  set Qj : ℝ := Q * (1 + η) ^ j with hQj
  have hr1 : (1 : ℝ) ≤ 1 + η := by linarith
  have hQj0 : (0 : ℝ) < Qj := by
    rw [hQj]
    have : (0 : ℝ) < (1 + η) ^ j := by positivity
    positivity
  have hsub : geomBlock P Q (1 + η) j ⊆ Finset.Icc (⌊Qj⌋₊ + 1) ⌊Qj * (1 + η)⌋₊ := by
    intro p hp
    rw [geomBlock, Finset.mem_filter] at hp
    obtain ⟨-, hlo, hhi⟩ := hp
    have hpow : Q * (1 + η) ^ (j + 1) = Qj * (1 + η) := by
      rw [hQj, pow_succ]
      ring
    rw [hpow] at hhi
    rw [← hQj] at hlo
    refine Finset.mem_Icc.2 ⟨?_, Nat.le_floor hhi⟩
    have hfl : ((⌊Qj⌋₊ : ℕ) : ℝ) ≤ Qj := Nat.floor_le hQj0.le
    have : (⌊Qj⌋₊ : ℕ) < p := by exact_mod_cast lt_of_le_of_lt hfl hlo
    omega
  have hcard : ((geomBlock P Q (1 + η) j).card : ℝ)
      ≤ ((Finset.Icc (⌊Qj⌋₊ + 1) ⌊Qj * (1 + η)⌋₊).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  refine hcard.trans ?_
  have hlo : Qj ≤ ((⌊Qj⌋₊ + 1 : ℕ) : ℝ) := by
    push_cast
    exact (Nat.lt_floor_add_one Qj).le
  have hhi : ((⌊Qj * (1 + η)⌋₊ : ℕ) : ℝ) ≤ Qj * (1 + η) :=
    Nat.floor_le (by positivity)
  have hbound := card_Icc_cast_le hlo hhi (by nlinarith [hQj0, hη])
  refine hbound.trans (le_of_eq ?_)
  ring

/-! ## The size of one gap set -/

/-- **A gap set is the discrepancy of one cofactor set against the common block of its step.** -/
theorem card_ladderGapSet_le {P : Finset ℕ} (M : ℕ) {Q η : ℝ} (hQ : 0 < Q) (hη : 0 ≤ η)
    {L : ℕ} {x : (_ : ℕ) × ℕ} (hx : x ∈ ladderIndex P Q η L)
    (hPprime : ∀ q ∈ P, q.Prime) :
    ((ladderGapSet M Q η x).card : ℝ)
      ≤ (((1 : ℕ) : ℝ) + ((M : ℕ) : ℝ)) * η / (Q * (1 + η) ^ x.1) + 4
        + (((M : ℕ) : ℝ) / (Q * (1 + η) ^ x.1) ^ 2 + 1) := by
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
  have hbase := card_cofactor_symmDiff_le (A₀ := 1) (B₀ := M) hQj0 hη hp.pos hlo hhi
  rw [ladderGapSet, geomCofactorBlock, ← hQj]
  exact hbase

/-! ## The total gap budget -/

/-- **The ladder gap budget.**  Summed over the flattened index, the gap sets cost the step size
times the per-prime discrepancy. -/
theorem sum_card_ladderGapSet_le {P : Finset ℕ} (M : ℕ) {Q η : ℝ} (hQ : 0 < Q) (hη : 0 ≤ η)
    (L : ℕ) (hPprime : ∀ q ∈ P, q.Prime) :
    (∑ x ∈ ladderIndex P Q η L, ((ladderGapSet M Q η x).card : ℝ))
      ≤ ∑ j ∈ Finset.range L, ((geomBlock P Q (1 + η) j).card : ℝ)
          * ((((1 : ℕ) : ℝ) + ((M : ℕ) : ℝ)) * η / (Q * (1 + η) ^ j) + 5
            + ((M : ℕ) : ℝ) / (Q * (1 + η) ^ j) ^ 2) := by
  classical
  have hstep : ∀ x ∈ ladderIndex P Q η L, ((ladderGapSet M Q η x).card : ℝ)
      ≤ (((1 : ℕ) : ℝ) + ((M : ℕ) : ℝ)) * η / (Q * (1 + η) ^ x.1) + 5
        + ((M : ℕ) : ℝ) / (Q * (1 + η) ^ x.1) ^ 2 := by
    intro x hx
    have h := card_ladderGapSet_le M hQ hη hx hPprime
    linarith
  refine (Finset.sum_le_sum hstep).trans (le_of_eq ?_)
  rw [ladderIndex, Finset.sum_sigma]
  refine Finset.sum_congr rfl fun j _ => ?_
  show (∑ _p ∈ geomBlock P Q (1 + η) j,
      ((((1 : ℕ) : ℝ) + ((M : ℕ) : ℝ)) * η / (Q * (1 + η) ^ j) + 5
        + ((M : ℕ) : ℝ) / (Q * (1 + η) ^ j) ^ 2)) = _
  rw [Finset.sum_const, nsmul_eq_mul]

/-- **The ladder gap budget, with the step sizes evaluated.** -/
theorem sum_card_ladderGapSet_le_explicit {P : Finset ℕ} (M : ℕ) {Q η : ℝ} (hQ : 0 < Q)
    (hη : 0 ≤ η) (L : ℕ) (hPprime : ∀ q ∈ P, q.Prime) :
    (∑ x ∈ ladderIndex P Q η L, ((ladderGapSet M Q η x).card : ℝ))
      ≤ ∑ j ∈ Finset.range L, (Q * (1 + η) ^ j * η + 1)
          * ((((1 : ℕ) : ℝ) + ((M : ℕ) : ℝ)) * η / (Q * (1 + η) ^ j) + 5
            + ((M : ℕ) : ℝ) / (Q * (1 + η) ^ j) ^ 2) := by
  refine (sum_card_ladderGapSet_le M hQ hη L hPprime).trans (Finset.sum_le_sum fun j _ => ?_)
  have hQj0 : (0 : ℝ) < Q * (1 + η) ^ j := by
    have : (0 : ℝ) < (1 + η) ^ j := by positivity
    positivity
  have hfac : (0 : ℝ) ≤ (((1 : ℕ) : ℝ) + ((M : ℕ) : ℝ)) * η / (Q * (1 + η) ^ j) + 5
      + ((M : ℕ) : ℝ) / (Q * (1 + η) ^ j) ^ 2 := by
    have h1 : (0 : ℝ) ≤ (((1 : ℕ) : ℝ) + ((M : ℕ) : ℝ)) * η / (Q * (1 + η) ^ j) := by positivity
    have h2 : (0 : ℝ) ≤ ((M : ℕ) : ℝ) / (Q * (1 + η) ^ j) ^ 2 := by positivity
    linarith
  exact mul_le_mul_of_nonneg_right (card_geomBlock_le P hQ hη j) hfac

/-! ## The ladder error, closed -/

/-- **The mean square of the ladder error, in closed form.**  Every quantity is explicit in
`M`, `Q`, `η`, `L` and the window `W`. -/
theorem integral_normSq_ramareLadderError_le_closed {P : Finset ℕ} (M : ℕ) {Q η W : ℝ}
    (hQ : 1 < Q) (hη : 0 ≤ η) (hW : 1 ≤ W) {L : ℕ}
    (hPprime : ∀ q ∈ P, q.Prime) (hPge : ∀ p ∈ P, Q ≤ (p : ℝ)) :
    (∫ w in Set.Icc (-W) W, ‖ramareLadderError P M Q η L w‖ ^ 2)
      ≤ (5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * ((⌊(M : ℝ) * (1 + η)⌋₊ : ℕ) : ℝ))
          * (Real.log ((⌊(M : ℝ) * (1 + η)⌋₊ : ℕ) : ℝ) / Real.log Q
            * ∑ j ∈ Finset.range L, (Q * (1 + η) ^ j * η + 1)
                * ((((1 : ℕ) : ℝ) + ((M : ℕ) : ℝ)) * η / (Q * (1 + η) ^ j) + 5
                  + ((M : ℕ) : ℝ) / (Q * (1 + η) ^ j) ^ 2)) := by
  classical
  have hQ0 : (0 : ℝ) < Q := lt_trans zero_lt_one hQ
  have hlogQ : 0 < Real.log Q := Real.log_pos hQ
  set N : ℕ := ⌊(M : ℝ) * (1 + η)⌋₊ with hN
  have hK0 : (0 : ℝ) ≤ Real.log ((N : ℕ) : ℝ) / Real.log Q :=
    div_nonneg (Real.log_natCast_nonneg N) hlogQ.le
  have hKmem : ∀ n ∈ Finset.Icc 1 N, ((P.filter (fun p => p ∣ n)).card : ℝ)
      ≤ Real.log ((N : ℕ) : ℝ) / Real.log Q := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    exact card_designatedPrimes_dvd_le hQ hPprime hPge hn.1 hn.2
  have hmain := integral_normSq_ramareLadderError_le_divisorCount (P := P) (L := L) M hQ.le hη hW
    hK0 hPprime hKmem
  refine hmain.trans ?_
  have hcoef : (0 : ℝ) ≤ 5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * ((N : ℕ) : ℝ) := by
    have hW0 : (0 : ℝ) < W := lt_of_lt_of_le zero_lt_one hW
    have h1 : (0 : ℝ) ≤ 5 * Real.pi / 2 * W := mul_nonneg (by positivity) hW0.le
    have h2 : (0 : ℝ) ≤ 5 * Real.exp 1 / 2 * ((N : ℕ) : ℝ) :=
      mul_nonneg (by positivity) (Nat.cast_nonneg N)
    linarith
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hK0) hcoef
  exact sum_card_ladderGapSet_le_explicit M hQ0 hη L hPprime

end

end RHTower.Sieve
