import GaloisForLFunctions.RHTower.XiHeightAdaptiveFiniteLadder
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Height-adaptive linear--quadratic census collision

In a bounded right-half Xi box, the difference between the quadratic multiplicity census
`Q = sum m_z^2` and the linear census `M = sum m_z` is the nonnegative nonsimplicity excess
`sum m_z(m_z-1)`.  Equality of the two censuses modulo one height-adapted modulus above the squared
zero-count envelope forces all enclosed zeros to be simple.  The first RH ladder rung forces every
right-half multiplicity to be even, so the two constraints together prove RH.

This file proves the collision implication, not either source premise.
-/

open Complex Metric Set

namespace RHTower

noncomputable section

def boxSquareOrderSum (T : ℝ) : ℕ :=
  ∑ z ∈ boxFinset T, ((analyticOrderAt xi z).toNat) ^ 2

def quadraticDiscCensusH (k : ℕ) (T : ℝ) : ZMod (2 ^ k) :=
  (boxSquareOrderSum T : ZMod (2 ^ k))

def boxMultiplicityExcessSum (T : ℝ) : ℕ :=
  ∑ z ∈ boxFinset T,
    (analyticOrderAt xi z).toNat * ((analyticOrderAt xi z).toNat - 1)

theorem boxSquareOrderSum_eq_order_add_excess (T : ℝ) :
    boxSquareOrderSum T = boxOrderSum T + boxMultiplicityExcessSum T := by
  rw [boxSquareOrderSum, boxOrderSum, boxMultiplicityExcessSum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro z hz
  have hpos : 0 < (analyticOrderAt xi z).toNat :=
    Nat.pos_of_ne_zero (xi_order_toNat_ne_zero (mem_boxFinset.mp hz).2)
  have hm : (analyticOrderAt xi z).toNat =
      1 + ((analyticOrderAt xi z).toNat - 1) := by omega
  calc
    (analyticOrderAt xi z).toNat ^ 2 =
        (analyticOrderAt xi z).toNat * (analyticOrderAt xi z).toNat := by ring
    _ = (analyticOrderAt xi z).toNat *
        (1 + ((analyticOrderAt xi z).toNat - 1)) := by rw [← hm]
    _ = (analyticOrderAt xi z).toNat +
        (analyticOrderAt xi z).toNat * ((analyticOrderAt xi z).toNat - 1) := by ring

theorem boxOrderSum_le_boxSquareOrderSum (T : ℝ) :
    boxOrderSum T ≤ boxSquareOrderSum T := by
  rw [boxSquareOrderSum_eq_order_add_excess]
  omega

theorem boxSquareOrderSum_le_sq_boxOrderSum (T : ℝ) :
    boxSquareOrderSum T ≤ (boxOrderSum T) ^ 2 := by
  rw [boxSquareOrderSum, boxOrderSum]
  exact Finset.sum_sq_le_sq_sum_of_nonneg fun _ _ => Nat.zero_le _

theorem boxSquareOrderSum_eq_boxOrderSum_iff_all_simple (T : ℝ) :
    boxSquareOrderSum T = boxOrderSum T ↔
      ∀ z ∈ boxFinset T, (analyticOrderAt xi z).toNat = 1 := by
  constructor
  · intro heq z hz
    have hexcess : boxMultiplicityExcessSum T = 0 := by
      rw [boxSquareOrderSum_eq_order_add_excess] at heq
      omega
    have hterm := (Finset.sum_eq_zero_iff.mp
      (show (∑ u ∈ boxFinset T,
        (analyticOrderAt xi u).toNat * ((analyticOrderAt xi u).toNat - 1)) = 0 by
          exact hexcess)) z hz
    have hpos : 0 < (analyticOrderAt xi z).toNat :=
      Nat.pos_of_ne_zero (xi_order_toNat_ne_zero (mem_boxFinset.mp hz).2)
    rcases Nat.mul_eq_zero.mp hterm with hzero | hpred
    · omega
    · omega
  · intro hs
    rw [boxSquareOrderSum, boxOrderSum]
    apply Finset.sum_congr rfl
    intro z hz
    rw [hs z hz]
    norm_num

def XiNatHeightAdaptiveLinearQuadraticCensus (C : ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    ∃ k : ℕ,
      (C * (1 + ((n : ℝ) + 2)) * Real.log (2 + ((n : ℝ) + 2))) ^ 2 <
        (2 ^ k : ℕ) ∧
      quadraticDiscCensusH k (n : ℝ) = discCensusH k (n : ℝ)

theorem riemannHypothesis_of_rhLadder_one_of_xiNatHeightAdaptiveLinearQuadraticCensus_of_zeroCountBound
    {C : ℝ}
    (hcount : ∀ r : ℝ, 1 ≤ r →
      ((xiBallOrderSum (2 : ℂ) r : ℤ) : ℝ) ≤
        C * (1 + r) * Real.log (2 + r))
    (hcensus : XiNatHeightAdaptiveLinearQuadraticCensus C)
    (hladder : RHLadder 1) :
    RiemannHypothesis := by
  have hempty : ∀ n : ℕ, 1 ≤ n → boxZeros (n : ℝ) = ∅ := by
    intro n hn
    obtain ⟨k, hkLarge, hcensusEq⟩ := hcensus n hn
    have hmod : boxSquareOrderSum (n : ℝ) ≡ boxOrderSum (n : ℝ) [MOD 2 ^ k] := by
      exact (ZMod.natCast_eq_natCast_iff _ _ _).mp hcensusEq
    have hdecomp := boxSquareOrderSum_eq_order_add_excess (n : ℝ)
    have hdvd : 2 ^ k ∣ boxMultiplicityExcessSum (n : ℝ) := by
      have hmod' : boxOrderSum (n : ℝ) + boxMultiplicityExcessSum (n : ℝ) ≡
          boxOrderSum (n : ℝ) + 0 [MOD 2 ^ k] := by
        rw [← hdecomp]
        simpa using hmod
      exact Nat.modEq_zero_iff_dvd.mp
        (Nat.ModEq.add_left_cancel Nat.ModEq.rfl hmod')
    have hMInt := boxOrderSum_le_xiBallOrderSum (T := (n : ℝ))
    have hMReal : (boxOrderSum (n : ℝ) : ℝ) ≤
        C * (1 + ((n : ℝ) + 2)) * Real.log (2 + ((n : ℝ) + 2)) := by
      have hr1 : (1 : ℝ) ≤ (n : ℝ) + 2 := by
        have hn0 : (0 : ℝ) ≤ n := by positivity
        linarith
      have hcast : (boxOrderSum (n : ℝ) : ℝ) ≤
          ((xiBallOrderSum (2 : ℂ) ((n : ℝ) + 2) : ℤ) : ℝ) := by
        exact_mod_cast hMInt
      exact hcast.trans (hcount _ hr1)
    have hQnat : boxSquareOrderSum (n : ℝ) ≤ (boxOrderSum (n : ℝ)) ^ 2 :=
      boxSquareOrderSum_le_sq_boxOrderSum _
    have hQReal : (boxSquareOrderSum (n : ℝ) : ℝ) ≤
        (boxOrderSum (n : ℝ) : ℝ) ^ 2 := by exact_mod_cast hQnat
    have hE0 : 0 ≤ C * (1 + ((n : ℝ) + 2)) *
        Real.log (2 + ((n : ℝ) + 2)) :=
      (Nat.cast_nonneg (boxOrderSum (n : ℝ))).trans hMReal
    have hMsq : (boxOrderSum (n : ℝ) : ℝ) ^ 2 ≤
        (C * (1 + ((n : ℝ) + 2)) * Real.log (2 + ((n : ℝ) + 2))) ^ 2 := by
      nlinarith [Nat.cast_nonneg (α := ℝ) (boxOrderSum (n : ℝ))]
    have hQltReal : (boxSquareOrderSum (n : ℝ) : ℝ) < ((2 ^ k : ℕ) : ℝ) :=
      lt_of_le_of_lt (hQReal.trans hMsq) hkLarge
    have hQlt : boxSquareOrderSum (n : ℝ) < 2 ^ k := by exact_mod_cast hQltReal
    have hexcess : boxMultiplicityExcessSum (n : ℝ) = 0 := by
      by_contra hne
      have hpos := Nat.pos_of_ne_zero hne
      have hle := Nat.le_of_dvd hpos hdvd
      have hexcessLe : boxMultiplicityExcessSum (n : ℝ) ≤
          boxSquareOrderSum (n : ℝ) := by
        rw [hdecomp]
        omega
      omega
    have heq : boxSquareOrderSum (n : ℝ) = boxOrderSum (n : ℝ) := by
      rw [hdecomp, hexcess, add_zero]
    have hsimple := (boxSquareOrderSum_eq_boxOrderSum_iff_all_simple _).mp heq
    rw [Set.eq_empty_iff_forall_notMem]
    intro z hz
    have hzfin : z ∈ boxFinset (n : ℝ) := mem_boxFinset.mpr hz
    have hone := hsimple z hzfin
    have heven := (rhLadder_one_iff_even_order.mp hladder) z
      (by rw [mem_rightHalf]; exact hz.1.1) hz.2
    rw [hone] at heven
    exact Nat.not_even_one heven
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

theorem riemannHypothesis_of_rhLadder_one_of_xiNatHeightAdaptiveLinearQuadraticCensus
    (hcensus : XiNatHeightAdaptiveLinearQuadraticCensus xiZeroCountEnvelopeConstant)
    (hladder : RHLadder 1) :
    RiemannHypothesis :=
  riemannHypothesis_of_rhLadder_one_of_xiNatHeightAdaptiveLinearQuadraticCensus_of_zeroCountBound
    xiBallOrderSum_le_zeroCountEnvelope hcensus hladder

end

end RHTower
