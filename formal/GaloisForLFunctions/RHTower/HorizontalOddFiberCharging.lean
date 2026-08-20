import GaloisForLFunctions.RHTower.HorizontalSingletonFiberCharging

/-!
# The odd-fibre charging law for horizontal singleton fibres

`HorizontalSingletonFiberCharging.lean` charges the spoiled *simple critical* ordinates against the
off-line census, giving `H_1 \ge N_{0,s} - (N - N_0)/2`.  That inequality needs two proportions:
the critical proportion and the simple-critical proportion.

There is a charging that needs only **one** quantity.  Off-line copies of a Xi zero come in
critical-line-reflected pairs, so the total fibre multiplicity `h(\gamma)` has the same parity as the
critical multiplicity at `\gamma`.  An ordinate with odd fibre is therefore either a singleton, or has
`h(\gamma) \ge 3` — an odd number other than one is at least three.  Distinct such ordinates have
disjoint fibres, so

```text
3 · O(T) ≤ 2 · H₁(T) + N(T),        i.e.   H₁(T) ≥ (3/2)·O(T) − N(T)/2,
```

where `O(T)` counts the ordinates in `(0, T]` with odd fibre.  The bound is non-vacuous exactly when
`liminf O(T)/N(T) > 1/3`, and `O(T)` dominates the number of sign changes of Hardy's `Z`, which is
what the sign-change and Levinson detectors produce natively — without a simple-zero refinement.
-/

open Complex Set


noncomputable section

namespace RHTower

/-- `O(T)`: the ordinates in `(0, T]` whose complete Xi fibre has **odd** total multiplicity.
Off-line copies come in reflected pairs, so an odd fibre forces odd critical multiplicity, hence a
critical-line zero; and an ordinate carries at most one critical-line point.  Counting the
critical-line zeros with odd fibre therefore counts these ordinates. -/
def xiOddFiberCount (T : ℝ) : ℕ :=
  ((stripFinsetPos T).filter
    (fun z => z.re = 1 / 2 ∧ Odd (xiHorizontalMultiplicity z.im))).card

theorem one_le_xiHorizontalMultiplicity_of_mem {T : ℝ} {z : ℂ} (hz : z ∈ stripFinsetPos T) :
    1 ≤ xiHorizontalMultiplicity z.im := by
  classical
  obtain ⟨h1, h2, _, _, hzero⟩ := mem_stripFinsetPos.mp hz
  have hmem : z ∈ stripHeightFinset z.im :=
    mem_stripHeightFinset.mpr ⟨h1, h2, rfl, hzero⟩
  have hord : 1 ≤ (analyticOrderAt xi z).toNat :=
    Nat.one_le_iff_ne_zero.mpr (xi_order_toNat_ne_zero hzero)
  calc 1 ≤ (analyticOrderAt xi z).toNat := hord
    _ ≤ ∑ w ∈ stripHeightFinset z.im, (analyticOrderAt xi w).toNat :=
        Finset.single_le_sum (f := fun w : ℂ => (analyticOrderAt xi w).toNat)
          (fun w _ => Nat.zero_le _) hmem
    _ = xiHorizontalMultiplicity z.im := rfl

/-- **The odd-fibre charging law.**  For every height `T`,

```text
3 · O(T) ≤ 2 · H₁(T) + N(T).
```

An ordinate whose fibre is odd is either a singleton — counted by `H₁` — or has fibre multiplicity
at least three, because an odd number other than one is at least three.  Distinct such ordinates
have disjoint fibres, and every fibre sits inside the census, so the total charge is at most
`N(T)`.  Unconditional. -/
theorem three_mul_xiOddFiberCount_le (T : ℝ) :
    3 * xiOddFiberCount T ≤ 2 * xiSingletonFiberCount T + xiPosZeroCount T := by
  classical
  set A : Finset ℂ :=
    (stripFinsetPos T).filter
      (fun z => z.re = 1 / 2 ∧ Odd (xiHorizontalMultiplicity z.im)) with hA
  set C : Finset ℂ := A.filter (fun z => xiHorizontalMultiplicity z.im = 1) with hC
  set B : Finset ℂ := A.filter (fun z => ¬ xiHorizontalMultiplicity z.im = 1) with hB
  have hcard : C.card + B.card = A.card := by
    rw [hB, hC]; exact Finset.card_filter_add_card_filter_not _
  have hAmem : ∀ z ∈ A, z ∈ stripFinsetPos T ∧ z.re = 1 / 2 ∧
      Odd (xiHorizontalMultiplicity z.im) := by
    intro z hz
    rw [hA, Finset.mem_filter] at hz
    exact ⟨hz.1, hz.2.1, hz.2.2⟩
  -- the singleton part is charged to `H₁`
  have hCle : C.card ≤ xiSingletonFiberCount T := by
    refine Finset.card_le_card ?_
    intro z hz
    rw [hC, Finset.mem_filter] at hz
    exact Finset.mem_filter.mpr ⟨(hAmem z hz.1).1, hz.2⟩
  -- distinct critical-line points have distinct ordinates, so their fibres are disjoint
  have hdisj : (A : Set ℂ).PairwiseDisjoint (fun z => stripHeightFinset z.im) := by
    intro z hz z' hz' hne
    have hzre := (hAmem z (Finset.mem_coe.mp hz)).2.1
    have hz're := (hAmem z' (Finset.mem_coe.mp hz')).2.1
    refine Finset.disjoint_left.mpr ?_
    intro w hw hw'
    have h1 : w.im = z.im := (mem_stripHeightFinset.mp hw).2.2.1
    have h2 : w.im = z'.im := (mem_stripHeightFinset.mp hw').2.2.1
    exact hne (Complex.ext (by rw [hzre, hz're]) (by rw [← h1, h2]))
  have hsub : A.biUnion (fun z => stripHeightFinset z.im) ⊆ stripFinsetPos T := by
    intro w hw
    obtain ⟨z, hz, hwz⟩ := Finset.mem_biUnion.mp hw
    obtain ⟨hzmem, _, _⟩ := hAmem z hz
    obtain ⟨_, _, hzpos, hzle, _⟩ := mem_stripFinsetPos.mp hzmem
    obtain ⟨h1, h2, him, hzero⟩ := mem_stripHeightFinset.mp hwz
    refine mem_stripFinsetPos.mpr ⟨h1, h2, ?_, ?_, hzero⟩
    · rw [him]; exact hzpos
    · rw [him]; exact hzle
  -- the total fibre charge is at most the census
  have hsum : ∑ z ∈ A, xiHorizontalMultiplicity z.im ≤ xiPosZeroCount T := by
    have h3 : ∑ z ∈ A, ∑ w ∈ stripHeightFinset z.im, (analyticOrderAt xi w).toNat
        = ∑ w ∈ A.biUnion (fun z => stripHeightFinset z.im), (analyticOrderAt xi w).toNat :=
      (Finset.sum_biUnion hdisj).symm
    have h4 : ∑ w ∈ A.biUnion (fun z => stripHeightFinset z.im), (analyticOrderAt xi w).toNat
        ≤ xiPosZeroCount T :=
      Finset.sum_le_sum_of_subset hsub
    calc ∑ z ∈ A, xiHorizontalMultiplicity z.im
        = ∑ z ∈ A, ∑ w ∈ stripHeightFinset z.im, (analyticOrderAt xi w).toNat := rfl
      _ = _ := h3
      _ ≤ xiPosZeroCount T := h4
  -- an odd fibre other than the singleton has multiplicity at least three
  have hlow : ∀ z ∈ B, 3 ≤ xiHorizontalMultiplicity z.im := by
    intro z hz
    rw [hB, Finset.mem_filter] at hz
    obtain ⟨hzmem, _, hodd⟩ := hAmem z hz.1
    have h1 := one_le_xiHorizontalMultiplicity_of_mem hzmem
    obtain ⟨m, hm⟩ := hodd
    omega
  have hlowC : ∀ z ∈ C, 1 ≤ xiHorizontalMultiplicity z.im := by
    intro z hz
    rw [hC, Finset.mem_filter] at hz
    exact le_of_eq hz.2.symm
  have hsplitsum : ∑ z ∈ A, xiHorizontalMultiplicity z.im
      = (∑ z ∈ C, xiHorizontalMultiplicity z.im) + ∑ z ∈ B, xiHorizontalMultiplicity z.im := by
    rw [hC, hB]
    exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hCsum : C.card ≤ ∑ z ∈ C, xiHorizontalMultiplicity z.im := by
    calc C.card = ∑ _z ∈ C, 1 := by rw [Finset.sum_const, smul_eq_mul, mul_one]
      _ ≤ ∑ z ∈ C, xiHorizontalMultiplicity z.im := Finset.sum_le_sum hlowC
  have hBsum : 3 * B.card ≤ ∑ z ∈ B, xiHorizontalMultiplicity z.im := by
    calc 3 * B.card = ∑ _z ∈ B, 3 := by rw [Finset.sum_const, smul_eq_mul]; ring
      _ ≤ ∑ z ∈ B, xiHorizontalMultiplicity z.im := Finset.sum_le_sum hlow
  have hAcard : A.card = xiOddFiberCount T := rfl
  omega

/-- **The odd-fibre charging law over `ℝ`.**  `H₁(T) ≥ (3/2)·O(T) − N(T)/2`. -/
theorem xiOddFiberCount_charge_real (T : ℝ) :
    (3 / 2 : ℝ) * (xiOddFiberCount T : ℝ) - (xiPosZeroCount T : ℝ) / 2
      ≤ (xiSingletonFiberCount T : ℝ) := by
  have h := three_mul_xiOddFiberCount_le T
  have hR : (3 : ℝ) * (xiOddFiberCount T : ℝ)
      ≤ 2 * (xiSingletonFiberCount T : ℝ) + (xiPosZeroCount T : ℝ) := by exact_mod_cast h
  linarith

/-! ## Normalized form -/

/-- `O(T)/N(T)`, the odd-fibre ordinate ratio. -/
def xiOddFiberRatio (T : ℝ) : ℝ := (xiOddFiberCount T : ℝ) / (xiPosZeroCount T : ℝ)

theorem xiOddFiberRatio_nonneg (T : ℝ) : 0 ≤ xiOddFiberRatio T := by
  unfold xiOddFiberRatio
  positivity

/-- **The normalized odd-fibre charging law.**  `H₁/N ≥ (3/2)·O/N − 1/2`, valid at every height,
including those with `N(T) = 0`. -/
theorem xiOddFiberRatio_charge (T : ℝ) :
    (3 / 2 : ℝ) * xiOddFiberRatio T - 1 / 2 ≤ xiSingletonFiberRatio T := by
  rcases Nat.eq_zero_or_pos (xiPosZeroCount T) with h0 | hpos
  · simp only [xiOddFiberRatio, xiSingletonFiberRatio, h0, Nat.cast_zero, div_zero]
    norm_num
  · have hn : (0 : ℝ) < (xiPosZeroCount T : ℝ) := by exact_mod_cast hpos
    have hR : (3 : ℝ) * (xiOddFiberCount T : ℝ)
        ≤ 2 * (xiSingletonFiberCount T : ℝ) + (xiPosZeroCount T : ℝ) := by
      exact_mod_cast three_mul_xiOddFiberCount_le T
    rw [← sub_nonneg]
    have hrw : xiSingletonFiberRatio T - ((3 / 2 : ℝ) * xiOddFiberRatio T - 1 / 2)
        = (2 * (xiSingletonFiberCount T : ℝ) + (xiPosZeroCount T : ℝ)
            - 3 * (xiOddFiberCount T : ℝ)) / (2 * (xiPosZeroCount T : ℝ)) := by
      rw [xiSingletonFiberRatio, xiOddFiberRatio]
      field_simp
      ring
    rw [hrw]
    apply div_nonneg (by linarith) (by linarith)

end RHTower

end
