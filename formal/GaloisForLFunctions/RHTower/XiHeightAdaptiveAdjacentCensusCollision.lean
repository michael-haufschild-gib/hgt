import GaloisForLFunctions.RHTower.XiHeightAdaptiveFiniteLadder
import GaloisForLFunctions.RHTower.CCMSharpPrimeWindowParityCollision

/-!
# Height-adaptive adjacent divisor-census collision

The pole-cancelled dyadic sharp source loses exactly one order at every shifted right-half Xi zero.
Summed over a bounded right-half box, this gives an exact decomposition

`Xi total order = cancelled-source common order + number of distinct Xi zeros`.

It follows that the earlier height-adaptive *vanishing* DISC census can be weakened in a different
direction.  It is enough that the Xi order census equal the cancelled-source common-order census
modulo one height-dependent power of two larger than the unconditional zero-count envelope.  Their
difference is then both the number of distinct zeros and a multiple of a larger positive modulus,
so the box is empty.  Integer-height exhaustion proves RH.

This module proves the reduction, not the source boundary congruence.  In particular it does not
construct a Kummer root, classify the Xi divisor, or assume local multiplicity divisibility.
-/

open Complex Metric Set

namespace RHTower

noncomputable section

/-- At a right-half Xi zero in a box, the shifted cancelled sharp source has precisely the
predecessor of the Xi vanishing order. -/
theorem cancelledSource_shift_order_eq_pred_of_mem_boxFinset
    {T : ℝ} {z : ℂ} (hz : z ∈ boxFinset T) :
    (analyticOrderAt dyadicSharpPrimeCancelledSource (z + 1 / 2)).toNat =
      (analyticOrderAt xi z).toNat - 1 := by
  have hzbox := mem_boxFinset.mp hz
  let support : XiDivisorSupport :=
    ⟨z, mem_xi_divisor_support_of_eq_zero hzbox.2⟩
  have hpos := xi_divisor_pos_on_support support
  have hn : 0 < Int.toNat
      ((MeromorphicOn.divisor xi Set.univ) (support : ℂ)) := by omega
  let q0 : XiZeroCopy := ⟨support, ⟨0, hn⟩⟩
  let q : XiRightZeroCopy := ⟨q0, by
    rw [I_mul_xiSpectralPoint]
    dsimp only [q0, support]
    rw [Complex.sub_re]
    norm_num
    exact hzbox.1.1⟩
  have hp : xiRightShiftedPole q = z + 1 / 2 := by
    rw [xiRightShiftedPole, xiRightCenteredZero_eq_support_sub_half]
    dsimp only [q, q0, support]
    ring
  obtain ⟨m, hreg, hcancel⟩ :=
    analyticOrderAt_dyadicSharpPrimeCancelledSource_eq_pred q
  have hxi : analyticOrderAt xi z = (m + 1 : ℕ) := by
    have hbridge := analyticOrderAt_shiftedRegularizedZeta_eq_xi_order q
    have h := hbridge.symm.trans hreg
    simpa only [q, q0, support] using h
  rw [hp] at hcancel
  simp only [hcancel, hxi, ENat.toNat_coe]
  omega

/-- The sum of the predecessor multiplicities in a right-half Xi box. -/
def boxPredOrderSum (T : ℝ) : ℕ :=
  (boxFinset T).sum fun z => (analyticOrderAt xi z).toNat - 1

/-- The common-divisor order sum read from the explicit cancelled source at the shifted Xi-box
points.  Analytically, this is the box degree of the gcd divisor of the shifted regularized zeta
and its cancelled-source companion. -/
def boxCancelledSourceCommonOrderSum (T : ℝ) : ℕ :=
  (boxFinset T).sum fun z =>
    (analyticOrderAt dyadicSharpPrimeCancelledSource (z + 1 / 2)).toNat

/-- The cancelled-source common-divisor sum is exactly the predecessor-order sum. -/
theorem boxCancelledSourceCommonOrderSum_eq_pred (T : ℝ) :
    boxCancelledSourceCommonOrderSum T = boxPredOrderSum T := by
  apply Finset.sum_congr rfl
  intro z hz
  exact cancelledSource_shift_order_eq_pred_of_mem_boxFinset hz

/-- The number of distinct, rather than multiplicity-counted, right-half Xi zeros in the box. -/
def boxDistinctCount (T : ℝ) : ℕ :=
  (boxFinset T).card

/-- **Adjacent divisor decomposition.**  Removing one order at every distinct zero leaves the
cancelled-source predecessor divisor. -/
theorem boxOrderSum_eq_pred_add_distinct (T : ℝ) :
    boxOrderSum T = boxPredOrderSum T + boxDistinctCount T := by
  rw [boxOrderSum, boxPredOrderSum, boxDistinctCount]
  calc
    ∑ z ∈ boxFinset T, (analyticOrderAt xi z).toNat =
        ∑ z ∈ boxFinset T, ((analyticOrderAt xi z).toNat - 1 + 1) := by
      apply Finset.sum_congr rfl
      intro z hz
      exact (Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr
        (xi_order_toNat_ne_zero (mem_boxFinset.mp hz).2))).symm
    _ = ((boxFinset T).sum fun z => (analyticOrderAt xi z).toNat - 1) +
        (boxFinset T).card := by simp [Finset.sum_add_distrib]

/-- The predecessor divisor reduced modulo the height-adapted dyadic modulus. -/
def predDiscCensusH (k : ℕ) (T : ℝ) : ZMod (2 ^ k) :=
  (boxPredOrderSum T : ZMod (2 ^ k))

/-- The shifted cancelled-source common-divisor census. -/
def cancelledSourceCommonCensusH (k : ℕ) (T : ℝ) : ZMod (2 ^ k) :=
  (boxCancelledSourceCommonOrderSum T : ZMod (2 ^ k))

theorem cancelledSourceCommonCensusH_eq_pred (k : ℕ) (T : ℝ) :
    cancelledSourceCommonCensusH k T = predDiscCensusH k T := by
  rw [cancelledSourceCommonCensusH, predDiscCensusH,
    boxCancelledSourceCommonOrderSum_eq_pred]

/-- At every integer height, choose one dyadic modulus above the unconditional zero-count envelope
for which the Xi divisor census and the cancelled-source common-divisor census agree. -/
def XiNatHeightAdaptiveAdjacentCensus (C : ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    ∃ k : ℕ,
      C * (1 + ((n : ℝ) + 2)) * Real.log (2 + ((n : ℝ) + 2)) <
        (2 ^ k : ℕ) ∧
      discCensusH k (n : ℝ) = cancelledSourceCommonCensusH k (n : ℝ)

/-- One adjacent census equality above any valid Xi zero-count envelope empties every integer box
and proves RH. -/
theorem riemannHypothesis_of_xiNatHeightAdaptiveAdjacentCensus_of_zeroCountBound
    {C : ℝ}
    (hcount : ∀ r : ℝ, 1 ≤ r →
      ((xiBallOrderSum (2 : ℂ) r : ℤ) : ℝ) ≤
        C * (1 + r) * Real.log (2 + r))
    (hcensus : XiNatHeightAdaptiveAdjacentCensus C) :
    RiemannHypothesis := by
  have hempty : ∀ n : ℕ, 1 ≤ n → boxZeros (n : ℝ) = ∅ := by
    intro n hn
    obtain ⟨k, hkLarge, hcensusEq⟩ := hcensus n hn
    rw [cancelledSourceCommonCensusH_eq_pred] at hcensusEq
    have hmod : boxOrderSum (n : ℝ) ≡ boxPredOrderSum (n : ℝ) [MOD 2 ^ k] := by
      exact (ZMod.natCast_eq_natCast_iff _ _ _).mp hcensusEq
    have hsum := boxOrderSum_eq_pred_add_distinct (n : ℝ)
    have hdvd : 2 ^ k ∣ boxDistinctCount (n : ℝ) := by
      rw [hsum] at hmod
      have hmod' : boxPredOrderSum (n : ℝ) + boxDistinctCount (n : ℝ) ≡
          boxPredOrderSum (n : ℝ) + 0 [MOD 2 ^ k] := by simpa using hmod
      exact Nat.modEq_zero_iff_dvd.mp
        (Nat.ModEq.add_left_cancel Nat.ModEq.rfl hmod')
    have hcardLe : boxDistinctCount (n : ℝ) ≤ boxOrderSum (n : ℝ) := by
      rw [boxOrderSum_eq_pred_add_distinct]
      omega
    have hboxInt := boxOrderSum_le_xiBallOrderSum (T := (n : ℝ))
    have hcardInt : (boxDistinctCount (n : ℝ) : ℤ) ≤
        (boxOrderSum (n : ℝ) : ℤ) := by exact_mod_cast hcardLe
    have hcardReal : (boxDistinctCount (n : ℝ) : ℝ) ≤
        ((xiBallOrderSum (2 : ℂ) ((n : ℝ) + 2) : ℤ) : ℝ) := by
      exact_mod_cast hcardInt.trans hboxInt
    have hr1 : (1 : ℝ) ≤ (n : ℝ) + 2 := by
      have hn0 : (0 : ℝ) ≤ n := by positivity
      linarith
    have hcardLtReal : (boxDistinctCount (n : ℝ) : ℝ) < ((2 ^ k : ℕ) : ℝ) :=
      lt_of_le_of_lt (hcardReal.trans (hcount _ hr1)) hkLarge
    have hcardLt : boxDistinctCount (n : ℝ) < 2 ^ k := by exact_mod_cast hcardLtReal
    have hcardZero : boxDistinctCount (n : ℝ) = 0 := by
      by_contra hne
      have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hdvd
      omega
    rw [boxDistinctCount, Finset.card_eq_zero] at hcardZero
    rw [Set.eq_empty_iff_forall_notMem]
    intro z hz
    have hzfin : z ∈ boxFinset (n : ℝ) := mem_boxFinset.mpr hz
    rw [hcardZero] at hzfin
    exact Finset.notMem_empty z hzfin
  rw [rh_iff_forall_boxZeros_empty]
  intro T
  obtain ⟨n : ℕ, hnT⟩ := exists_nat_gt (max 1 T)
  have hn1 : 1 ≤ n := by
    exact_mod_cast (lt_of_le_of_lt (le_max_left (1 : ℝ) T) hnT).le
  have hsubset : boxZeros T ⊆ boxZeros (n : ℝ) :=
    boxZeros_mono (le_trans (le_max_right (1 : ℝ) T) hnT.le)
  exact Set.eq_empty_iff_forall_notMem.mpr fun z hz => by
    have hz' := hsubset hz
    rw [hempty n hn1] at hz'
    exact Set.notMem_empty z hz'

/-- **Height-adaptive adjacent-census RH capstone.** -/
theorem riemannHypothesis_of_xiNatHeightAdaptiveAdjacentCensus
    (hcensus : XiNatHeightAdaptiveAdjacentCensus xiZeroCountEnvelopeConstant) :
    RiemannHypothesis :=
  riemannHypothesis_of_xiNatHeightAdaptiveAdjacentCensus_of_zeroCountBound
    xiBallOrderSum_le_zeroCountEnvelope hcensus

end

end RHTower
