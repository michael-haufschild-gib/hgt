import GaloisForLFunctions.RHTower.HorizontalFibreParity
import GaloisForLFunctions.RHTower.HorizontalOddFiberCharging

/-!
# Odd fibres are simple critical zeros up to a third of the census

An odd horizontal fibre carries a critical-line zero of odd order.  If that order is not `1` it is
at least `3`, and those copies are charged against the whole census.  Hence

```text
3·O(T) ≤ 3·N₀,s(T) + N(T),
```

so a lower density of odd fibres exceeding `1/3` forces a *positive* lower density of **simple**
critical zeros — the input the bounded-support Weil uniqueness card consumes.
-/

open Complex Set

noncomputable section

namespace RHTower

theorem eq_linePt_of_re_eq_half {z : ℂ} (hz : z.re = 1 / 2) : z = linePt z.im := by
  refine Complex.ext ?_ ?_
  · rw [hz]; simp [linePt]
  · simp [linePt]

/-- **Odd fibres are simple critical zeros, up to a third of the census.** -/
theorem three_mul_xiOddFiberCount_le_simple (T : ℝ) :
    3 * xiOddFiberCount T ≤ 3 * xiSimpleCriticalZeroCount T + xiPosZeroCount T := by
  classical
  set A : Finset ℂ := (stripFinsetPos T).filter
    (fun z => z.re = 1 / 2 ∧ Odd (xiHorizontalMultiplicity z.im)) with hA
  have hcard : A.card = (A.filter (fun z => (analyticOrderAt xi z).toNat = 1)).card
      + (A.filter (fun z => ¬ (analyticOrderAt xi z).toNat = 1)).card :=
    (Finset.card_filter_add_card_filter_not (s := A)
      (p := fun z => (analyticOrderAt xi z).toNat = 1)).symm
  -- the simple part
  have hsub1 : A.filter (fun z => (analyticOrderAt xi z).toNat = 1)
      ⊆ (stripFinsetPos T).filter (fun z => z.re = 1 / 2 ∧ (analyticOrderAt xi z).toNat = 1) := by
    intro z hz
    rw [Finset.mem_filter] at hz
    obtain ⟨hzA, hord⟩ := hz
    rw [hA, Finset.mem_filter] at hzA
    exact Finset.mem_filter.mpr ⟨hzA.1, hzA.2.1, hord⟩
  have hsimple : (A.filter (fun z => (analyticOrderAt xi z).toNat = 1)).card
      ≤ xiSimpleCriticalZeroCount T := Finset.card_le_card hsub1
  -- the high-order part
  have hthree : ∀ z ∈ A.filter (fun z => ¬ (analyticOrderAt xi z).toNat = 1),
      3 ≤ (analyticOrderAt xi z).toNat := by
    intro z hz
    rw [Finset.mem_filter] at hz
    obtain ⟨hzA, hord⟩ := hz
    rw [hA, Finset.mem_filter] at hzA
    obtain ⟨hmem, hre, hodd⟩ := hzA
    obtain ⟨_, _, _, _, hzero⟩ := mem_stripFinsetPos.mp hmem
    have hone : 1 ≤ (analyticOrderAt xi z).toNat :=
      Nat.one_le_iff_ne_zero.mpr (xi_order_toNat_ne_zero hzero)
    have hzeq : z = linePt z.im := eq_linePt_of_re_eq_half hre
    have hoddz : Odd ((analyticOrderAt xi z).toNat) := by
      rw [hzeq]
      exact (xiHorizontalMultiplicity_odd_iff z.im).mp hodd
    obtain ⟨k, hk⟩ := hoddz
    omega
  have hsum : 3 * (A.filter (fun z => ¬ (analyticOrderAt xi z).toNat = 1)).card
      ≤ ∑ z ∈ A.filter (fun z => ¬ (analyticOrderAt xi z).toNat = 1),
          (analyticOrderAt xi z).toNat := by
    calc 3 * (A.filter (fun z => ¬ (analyticOrderAt xi z).toNat = 1)).card
        = ∑ _z ∈ A.filter (fun z => ¬ (analyticOrderAt xi z).toNat = 1), 3 := by
          rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ z ∈ A.filter (fun z => ¬ (analyticOrderAt xi z).toNat = 1),
            (analyticOrderAt xi z).toNat := Finset.sum_le_sum hthree
  have hsubset : A.filter (fun z => ¬ (analyticOrderAt xi z).toNat = 1) ⊆ stripFinsetPos T := by
    intro z hz
    rw [Finset.mem_filter, hA, Finset.mem_filter] at hz
    exact hz.1.1
  have hcensus : (∑ z ∈ A.filter (fun z => ¬ (analyticOrderAt xi z).toNat = 1),
      (analyticOrderAt xi z).toNat) ≤ xiPosZeroCount T :=
    Finset.sum_le_sum_of_subset hsubset
  have hAcard : xiOddFiberCount T = A.card := by rw [hA, xiOddFiberCount]
  omega

end RHTower

end
