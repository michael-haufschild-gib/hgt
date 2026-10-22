import GaloisForLFunctions.RHTower.Suzuki.SuzukiSupportPrunedHistoryAction

/-!
# Cofinal literal chronology in the strict Suzuki seam

The fixed finite Suzuki boundary-excursion witnesses do not by themselves meet the route's
cofinal-history requirement.  This module supplies an explicit source family with no prime
distribution hypothesis.  At exponent `n + 1`, use the oriented prime-power steps

```text
δ = (n + 1) log 2,   η = -(n + 1) log 3,
q = (n + 1) log 5,   2a = (n + 1) log 10.
```

The forward intermediate coordinates are `(n + 1) log 5`,
`(n + 1) log (5/2)`, and `(n + 1) log (15/2)`, all strictly below the aperture edge.
The reversed intermediate coordinate is `(n + 1) log 15`, strictly above it.  Thus the literal
support-pruned source action has an ordered `1`/`0` readout above every prescribed aperture.

This proves source-side cofinal chronological supply only.  It does not claim a coefficient-
faithful transport into Route P, a terminal-current bound, or RH.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

private def cofinalHistoryTwo : Nat.Primes := ⟨2, Nat.prime_two⟩
private def cofinalHistoryThree : Nat.Primes := ⟨3, Nat.prime_three⟩
private def cofinalHistoryFive : Nat.Primes := ⟨5, by norm_num⟩

private def cofinalHistoryDelta (n : ℕ) : SuzukiSeamValuation :=
  suzukiPrimePowerStep (cofinalHistoryTwo, n + 1)

private def cofinalHistoryEta (n : ℕ) : SuzukiSeamValuation :=
  -suzukiPrimePowerStep (cofinalHistoryThree, n + 1)

private def cofinalHistoryReadout (n : ℕ) : SuzukiSeamVertex :=
  (SuzukiSeamRoot.left, suzukiPrimePowerStep (cofinalHistoryFive, n + 1))

private def cofinalHistoryAperture (n : ℕ) : ℝ :=
  ((n + 1 : ℕ) : ℝ) * Real.log 10 / 2

private theorem cofinalHistory_log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
private theorem cofinalHistory_log_three_pos : 0 < Real.log 3 := Real.log_pos (by norm_num)
private theorem cofinalHistory_log_five_pos : 0 < Real.log 5 := Real.log_pos (by norm_num)
private theorem cofinalHistory_log_ten_pos : 0 < Real.log 10 := Real.log_pos (by norm_num)

private theorem cofinalHistory_log_two_lt_log_five : Real.log 2 < Real.log 5 :=
  Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num)

private theorem cofinalHistory_log_five_lt_log_ten : Real.log 5 < Real.log 10 :=
  Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num)

private theorem cofinalHistory_log_three_lt_two_log_two : Real.log 3 < 2 * Real.log 2 := by
  have h : Real.log 3 < Real.log 4 :=
    Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num)
  calc
    Real.log 3 < Real.log 4 := h
    _ = Real.log (2 * 2) := by norm_num
    _ = Real.log 2 + Real.log 2 := by
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)]
      norm_num
    _ = 2 * Real.log 2 := by ring

private theorem cofinalHistory_log_five_add_log_three_eq_log_fifteen :
    Real.log 5 + Real.log 3 = Real.log 15 := by
  calc
    Real.log 5 + Real.log 3 = Real.log (5 * 3) := by
      rw [Real.log_mul (by norm_num : (5 : ℝ) ≠ 0)]
      norm_num
    _ = Real.log 15 := by norm_num

private theorem cofinalHistory_log_five_add_log_two_eq_log_ten :
    Real.log 5 + Real.log 2 = Real.log 10 := by
  calc
    Real.log 5 + Real.log 2 = Real.log (5 * 2) := by
      rw [Real.log_mul (by norm_num : (5 : ℝ) ≠ 0)]
      norm_num
    _ = Real.log 10 := by norm_num

private theorem cofinalHistory_log_ten_lt_log_fifteen : Real.log 10 < Real.log 15 :=
  Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num)

private theorem primeSeamCoordinate_cofinalHistoryDelta (n : ℕ) :
    primeSeamCoordinate (cofinalHistoryDelta n) = ((n + 1 : ℕ) : ℝ) * Real.log 2 := by
  simp [cofinalHistoryDelta, cofinalHistoryTwo, primeSeamCoordinate_primePowerStep]

private theorem primeSeamCoordinate_cofinalHistoryEta (n : ℕ) :
    primeSeamCoordinate (cofinalHistoryEta n) = -((n + 1 : ℕ) : ℝ) * Real.log 3 := by
  simp [cofinalHistoryEta, cofinalHistoryThree, primeSeamCoordinate_primePowerStep]
  ring

private theorem primeSeamCoordinate_cofinalHistoryReadout (n : ℕ) :
    primeSeamCoordinate (cofinalHistoryReadout n).2 = ((n + 1 : ℕ) : ℝ) * Real.log 5 := by
  simp [cofinalHistoryReadout, cofinalHistoryFive, primeSeamCoordinate_primePowerStep]

private theorem cofinalHistory_readout_mem (n : ℕ) :
    cofinalHistoryReadout n ∈ suzukiAdmissibleSeamVertices (cofinalHistoryAperture n) := by
  rw [suzukiAdmissibleSeamVertices_iff, primeSeamCoordinate_cofinalHistoryReadout,
    cofinalHistoryAperture]
  have hm : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  constructor
  · positivity
  · have hlt := mul_lt_mul_of_pos_left cofinalHistory_log_five_lt_log_ten hm
    nlinarith [hlt]

private theorem cofinalHistory_delta_predecessor_mem (n : ℕ) :
    ((cofinalHistoryReadout n).1, (cofinalHistoryReadout n).2 - cofinalHistoryDelta n) ∈
      suzukiAdmissibleSeamVertices (cofinalHistoryAperture n) := by
  rw [suzukiAdmissibleSeamVertices_iff]
  have hcoord :
      primeSeamCoordinate ((cofinalHistoryReadout n).2 - cofinalHistoryDelta n) =
        ((n + 1 : ℕ) : ℝ) * (Real.log 5 - Real.log 2) := by
    rw [map_sub, primeSeamCoordinate_cofinalHistoryReadout,
      primeSeamCoordinate_cofinalHistoryDelta]
    ring
  rw [hcoord, cofinalHistoryAperture]
  have hm : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  constructor
  · exact mul_pos hm (sub_pos.mpr cofinalHistory_log_two_lt_log_five)
  · have hlt : Real.log 5 - Real.log 2 < Real.log 10 := by
      linarith [cofinalHistory_log_two_pos, cofinalHistory_log_five_lt_log_ten]
    have hmul := mul_lt_mul_of_pos_left hlt hm
    nlinarith [hmul]

private theorem cofinalHistory_forward_predecessor_mem (n : ℕ) :
    ((cofinalHistoryReadout n).1,
      (cofinalHistoryReadout n).2 - cofinalHistoryDelta n - cofinalHistoryEta n) ∈
      suzukiAdmissibleSeamVertices (cofinalHistoryAperture n) := by
  rw [suzukiAdmissibleSeamVertices_iff]
  have hcoord :
      primeSeamCoordinate
          ((cofinalHistoryReadout n).2 - cofinalHistoryDelta n - cofinalHistoryEta n) =
        ((n + 1 : ℕ) : ℝ) * (Real.log 5 - Real.log 2 + Real.log 3) := by
    rw [map_sub, map_sub, primeSeamCoordinate_cofinalHistoryReadout,
      primeSeamCoordinate_cofinalHistoryDelta, primeSeamCoordinate_cofinalHistoryEta]
    ring
  rw [hcoord, cofinalHistoryAperture]
  have hm : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  constructor
  · have hpos : 0 < Real.log 5 - Real.log 2 + Real.log 3 := by
      linarith [cofinalHistory_log_two_lt_log_five, cofinalHistory_log_three_pos]
    exact mul_pos hm hpos
  · have hlt : Real.log 5 - Real.log 2 + Real.log 3 < Real.log 10 := by
      rw [← cofinalHistory_log_five_add_log_two_eq_log_ten]
      linarith [cofinalHistory_log_three_lt_two_log_two]
    have hmul := mul_lt_mul_of_pos_left hlt hm
    nlinarith [hmul]

private theorem cofinalHistory_reverse_predecessor_not_mem (n : ℕ) :
    ((cofinalHistoryReadout n).1, (cofinalHistoryReadout n).2 - cofinalHistoryEta n) ∉
      suzukiAdmissibleSeamVertices (cofinalHistoryAperture n) := by
  intro h
  rw [suzukiAdmissibleSeamVertices_iff] at h
  have hcoord :
      primeSeamCoordinate ((cofinalHistoryReadout n).2 - cofinalHistoryEta n) =
        ((n + 1 : ℕ) : ℝ) * (Real.log 5 + Real.log 3) := by
    rw [map_sub, primeSeamCoordinate_cofinalHistoryReadout,
      primeSeamCoordinate_cofinalHistoryEta]
    ring
  rw [hcoord, cofinalHistoryAperture] at h
  have hm : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have hlt : Real.log 10 < Real.log 5 + Real.log 3 := by
    rw [cofinalHistory_log_five_add_log_three_eq_log_fifteen]
    exact cofinalHistory_log_ten_lt_log_fifteen
  have hmul := mul_lt_mul_of_pos_left hlt hm
  nlinarith [hmul]

/-- The first positive literal leg of the cofinal pruned chronology at exponent `n + 1`. -/
def suzukiCofinalPrunedHistoryDelta (n : ℕ) : SuzukiSeamValuation :=
  cofinalHistoryDelta n

/-- The reflected literal leg of the cofinal pruned chronology at exponent `n + 1`. -/
def suzukiCofinalPrunedHistoryEta (n : ℕ) : SuzukiSeamValuation :=
  cofinalHistoryEta n

/-- Source readout vertex of the cofinal pruned chronology. -/
def suzukiCofinalPrunedHistoryReadout (n : ℕ) : SuzukiSeamVertex :=
  cofinalHistoryReadout n

/-- Strict aperture used by the cofinal pruned chronology at exponent `n + 1`. -/
def suzukiCofinalPrunedHistoryAperture (n : ℕ) : ℝ :=
  cofinalHistoryAperture n

/-- Literal seed supported at the forward two-leg predecessor of the cofinal chronology. -/
def suzukiCofinalPrunedHistorySeed (n : ℕ) : SuzukiSeamHilbert :=
  lp.single 2 ((cofinalHistoryReadout n).1,
    (cofinalHistoryReadout n).2 - cofinalHistoryDelta n - cofinalHistoryEta n) 1

/-- The cofinal source family has an explicit, not merely existential, ordered `1`/`0` readout.
Publishing this exact family keeps its prime-power labels available for synchronization with a
physical prime-power admission clock. -/
theorem suzukiCofinalPrunedHistory_ordered_value_asymmetry_at (n : ℕ) :
    suzukiOrientedSupportPrunedHistoryAction (suzukiCofinalPrunedHistoryAperture n)
        [suzukiCofinalPrunedHistoryDelta n, suzukiCofinalPrunedHistoryEta n]
        (suzukiCofinalPrunedHistorySeed n) (suzukiCofinalPrunedHistoryReadout n) = 1 ∧
      suzukiOrientedSupportPrunedHistoryAction (suzukiCofinalPrunedHistoryAperture n)
        [suzukiCofinalPrunedHistoryEta n, suzukiCofinalPrunedHistoryDelta n]
        (suzukiCofinalPrunedHistorySeed n) (suzukiCofinalPrunedHistoryReadout n) = 0 := by
  simpa [suzukiCofinalPrunedHistoryAperture, suzukiCofinalPrunedHistoryDelta,
    suzukiCofinalPrunedHistoryEta, suzukiCofinalPrunedHistorySeed,
    suzukiCofinalPrunedHistoryReadout, suzukiOrientedSupportPrunedHistoryAction] using
    suzukiOrientedSupportPrunedShift_ordered_path_asymmetry _ _ _ _
      (cofinalHistory_readout_mem n) (cofinalHistory_delta_predecessor_mem n)
      (cofinalHistory_forward_predecessor_mem n)
      (cofinalHistory_reverse_predecessor_not_mem n)

/-- **Cofinal source chronology.**  Above every real aperture threshold, literal strict Suzuki
support pruning has a prime-power-labelled two-letter history whose two orderings have readouts
`1` and `0`.  No PNT, density estimate, or scalar quotient enters. -/
theorem exists_suzukiCofinalPrunedHistory_ordered_value_asymmetry (A : ℝ) :
    ∃ (a : ℝ) (δ η : SuzukiSeamValuation) (f : SuzukiSeamHilbert)
      (q : SuzukiSeamVertex), A < a ∧ 0 < a ∧
      suzukiOrientedSupportPrunedHistoryAction a [δ, η] f q = 1 ∧
      suzukiOrientedSupportPrunedHistoryAction a [η, δ] f q = 0 := by
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * A / Real.log 10)
  refine ⟨cofinalHistoryAperture n, cofinalHistoryDelta n, cofinalHistoryEta n,
    lp.single 2 ((cofinalHistoryReadout n).1,
      (cofinalHistoryReadout n).2 - cofinalHistoryDelta n - cofinalHistoryEta n) 1,
    cofinalHistoryReadout n, ?_, ?_, ?_⟩
  · have hmul := (div_lt_iff₀ cofinalHistory_log_ten_pos).mp hn
    have hnle : (n : ℝ) * Real.log 10 ≤ ((n + 1 : ℕ) : ℝ) * Real.log 10 := by
      gcongr
      omega
    dsimp [cofinalHistoryAperture]
    linarith
  · unfold cofinalHistoryAperture
    positivity
  · simpa [suzukiOrientedSupportPrunedHistoryAction] using
      suzukiOrientedSupportPrunedShift_ordered_path_asymmetry _ _ _ _
        (cofinalHistory_readout_mem n) (cofinalHistory_delta_predecessor_mem n)
        (cofinalHistory_forward_predecessor_mem n)
        (cofinalHistory_reverse_predecessor_not_mem n)

end

end GaloisForLFunctions.RHTower
