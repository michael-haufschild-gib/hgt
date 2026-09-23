import GaloisForLFunctions.RHTower.XiHeightAdaptiveHedenmalmCensusCollision
import GaloisForLFunctions.RHTower.XiHeightAdaptiveLinearQuadraticCensusCollision

/-!
# Height-adaptive positive-defect census universality

The Hedenmalm adjacent census and the linear--quadratic census use different analytic sources, but
their arithmetic closure is identical.  An upper census splits as a lower census plus a
nonnegative defect; every nonempty right-half Xi box makes that defect positive.  If upper and
lower become congruent modulo one height-dependent power of two larger than the defect, the box is
empty.  Integer-height exhaustion then proves RH.

The law below isolates that common mechanism for arbitrary upper, lower, and defect censuses.  The
adjacent route has defect equal to the distinct-zero count.  The quadratic route has defect equal
to the nonsimplicity excess and uses the first ladder rung to make it positive on a nonempty box.
-/

open Complex Metric Set

namespace RHTower

noncomputable section

/-- Height-adaptive congruence of arbitrary upper and lower natural-valued box censuses. -/
def XiNatHeightAdaptivePositiveDefectCollision
    (bound : ℕ → ℝ) (upper lower : ℝ → ℕ) : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    ∃ k : ℕ,
      bound n < (2 ^ k : ℕ) ∧
      (upper (n : ℝ) : ZMod (2 ^ k)) =
        (lower (n : ℝ) : ZMod (2 ^ k))

/-- **Positive-defect census universality law.**  Any height-adaptive modular collision between
two censuses whose difference is a bounded, nonempty-box-detecting positive defect forces RH. -/
theorem riemannHypothesis_of_xiNatHeightAdaptivePositiveDefectCollision
    (bound : ℕ → ℝ) (upper lower defect : ℝ → ℕ)
    (hdecomp : ∀ T, upper T = lower T + defect T)
    (hdetect : ∀ T, (boxFinset T).Nonempty → 0 < defect T)
    (hbound : ∀ n : ℕ, 1 ≤ n → (defect (n : ℝ) : ℝ) ≤ bound n)
    (hcollision : XiNatHeightAdaptivePositiveDefectCollision bound upper lower) :
    RiemannHypothesis := by
  have hempty : ∀ n : ℕ, 1 ≤ n → boxZeros (n : ℝ) = ∅ := by
    intro n hn
    obtain ⟨k, hkLarge, hcensus⟩ := hcollision n hn
    have hmod : upper (n : ℝ) ≡ lower (n : ℝ) [MOD 2 ^ k] :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mp hcensus
    have hdvd : 2 ^ k ∣ defect (n : ℝ) := by
      rw [hdecomp] at hmod
      have hmod' : lower (n : ℝ) + defect (n : ℝ) ≡
          lower (n : ℝ) + 0 [MOD 2 ^ k] := by simpa using hmod
      exact Nat.modEq_zero_iff_dvd.mp
        (Nat.ModEq.add_left_cancel Nat.ModEq.rfl hmod')
    have hdefectLtReal : (defect (n : ℝ) : ℝ) < ((2 ^ k : ℕ) : ℝ) :=
      (hbound n hn).trans_lt hkLarge
    have hdefectLt : defect (n : ℝ) < 2 ^ k := by
      exact_mod_cast hdefectLtReal
    have hfinEmpty : boxFinset (n : ℝ) = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro z hz
      have hpositive : 0 < defect (n : ℝ) := hdetect _ ⟨z, hz⟩
      have hmodLe : 2 ^ k ≤ defect (n : ℝ) := Nat.le_of_dvd hpositive hdvd
      omega
    rw [Set.eq_empty_iff_forall_notMem]
    intro z hz
    have hzfin : z ∈ boxFinset (n : ℝ) := mem_boxFinset.mpr hz
    rw [hfinEmpty] at hzfin
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

/-- In the Hedenmalm route the upper-minus-lower defect is exactly the distinct-zero count. -/
theorem boxOrderSum_eq_hedenmalmCommon_add_distinct (T : ℝ) :
    boxOrderSum T = boxHedenmalmCommonOrderSum T + boxDistinctCount T := by
  rw [boxHedenmalmCommonOrderSum_eq_pred, boxOrderSum_eq_pred_add_distinct]

/-- The Hedenmalm adjacent hypothesis is an instance of the universal collision interface. -/
theorem xiNatHeightAdaptivePositiveDefectCollision_of_hedenmalm
    {C : ℝ} (h : XiNatHeightAdaptiveHedenmalmAdjacentCensus C) :
    XiNatHeightAdaptivePositiveDefectCollision
      (fun n => C * (1 + ((n : ℝ) + 2)) * Real.log (2 + ((n : ℝ) + 2)))
      boxOrderSum boxHedenmalmCommonOrderSum := by
  intro n hn
  obtain ⟨k, hk, hcensus⟩ := h n hn
  exact ⟨k, hk, by simpa [discCensusH, hedenmalmCommonCensusH] using hcensus⟩

/-- The linear--quadratic hypothesis is the same universal collision interface with the squared
zero-count envelope and nonsimplicity defect. -/
theorem xiNatHeightAdaptivePositiveDefectCollision_of_linearQuadratic
    {C : ℝ} (h : XiNatHeightAdaptiveLinearQuadraticCensus C) :
    XiNatHeightAdaptivePositiveDefectCollision
      (fun n =>
        (C * (1 + ((n : ℝ) + 2)) * Real.log (2 + ((n : ℝ) + 2))) ^ (2 : ℕ))
      boxSquareOrderSum boxOrderSum := by
  intro n hn
  obtain ⟨k, hk, hcensus⟩ := h n hn
  exact ⟨k, hk, by simpa [quadraticDiscCensusH, discCensusH] using hcensus⟩

end

end RHTower
