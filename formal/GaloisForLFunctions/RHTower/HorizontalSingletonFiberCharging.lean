import GaloisForLFunctions.RHTower.HorizontalSingletonZeroFiber

/-!
# The finite charging law for horizontal-singleton Xi fibers

`HorizontalSingletonZeroFiber.lean` proves the pointwise half of the horizontal-singleton theorem:
an ordinate whose complete Xi fiber has total multiplicity one carries exactly one zero, that zero
is simple, and it sits on the critical line.

This module proves the *global finite* half.  With

* `xiPosZeroCount T`               — `N(T)`, all strip Xi zeros with `0 < im ≤ T`, with multiplicity;
* `xiPosCriticalZeroCount T`       — `N₀(T)`, the critical-line copies;
* `xiOffLineZeroCount T`        — `N(T) − N₀(T)`, the off-line copies;
* `xiSimpleCriticalZeroCount T` — `N₀,s(T)`, the simple critical-line zeros;
* `xiSingletonFiberCount T`     — `H₁(T)`, the ordinates whose full fiber has multiplicity one,

the charging inequality

```text
2 (N₀,s(T) − H₁(T)) ≤ N(T) − N₀(T)
```

holds for every height `T`, unconditionally.  The mechanism: a simple critical zero whose ordinate
is *not* a singleton fiber must share that ordinate with an off-line zero, whose critical-line
reflection is a distinct zero of the same order at the same ordinate; so each spoiled simple
critical ordinate consumes at least two off-line copies, and distinct ordinates consume disjoint
copies.

Everything here is a statement about the actual `xi` divisor.  No hypothesis, no zero-density
input, and no unproved analytic proportion enters.
-/

open Complex Set

namespace RHTower

noncomputable section

/-! ## The four finite counts -/

/-- Strip Xi zeros with ordinate in `(0, T]`.  This is the divisor counted by `N(T)`. -/
def stripFinsetPos (T : ℝ) : Finset ℂ :=
  (stripFinsetLe T).filter (fun z => 0 < z.im)

theorem mem_stripFinsetPos {T : ℝ} {z : ℂ} :
    z ∈ stripFinsetPos T ↔ 0 < z.re ∧ z.re < 1 ∧ 0 < z.im ∧ z.im ≤ T ∧ xi z = 0 := by
  rw [stripFinsetPos, Finset.mem_filter, mem_stripFinsetLe]
  constructor
  · rintro ⟨⟨h1, h2, _, h4, hz⟩, hpos⟩
    exact ⟨h1, h2, hpos, h4, hz⟩
  · rintro ⟨h1, h2, hpos, h4, hz⟩
    exact ⟨⟨h1, h2, hpos.le, h4, hz⟩, hpos⟩

/-- `N(T)`: the number of nontrivial Xi zeros with ordinate in `(0, T]`, with multiplicity. -/
def xiPosZeroCount (T : ℝ) : ℕ :=
  ∑ z ∈ stripFinsetPos T, (analyticOrderAt xi z).toNat

/-- `N₀(T)`: the critical-line copies counted by `N(T)`. -/
def xiPosCriticalZeroCount (T : ℝ) : ℕ :=
  ∑ z ∈ (stripFinsetPos T).filter (fun z => z.re = 1 / 2), (analyticOrderAt xi z).toNat

/-- `N(T) − N₀(T)`: the off-line copies counted by `N(T)`. -/
def xiOffLineZeroCount (T : ℝ) : ℕ :=
  ∑ z ∈ (stripFinsetPos T).filter (fun z => ¬ z.re = 1 / 2), (analyticOrderAt xi z).toNat

/-- The census splits into its critical and off-line halves. -/
theorem xiPosCriticalZeroCount_add_xiOffLineZeroCount (T : ℝ) :
    xiPosCriticalZeroCount T + xiOffLineZeroCount T = xiPosZeroCount T :=
  Finset.sum_filter_add_sum_filter_not _ _ _

theorem xiPosCriticalZeroCount_le (T : ℝ) : xiPosCriticalZeroCount T ≤ xiPosZeroCount T := by
  rw [← xiPosCriticalZeroCount_add_xiOffLineZeroCount T]; exact Nat.le_add_right _ _

/-- `N₀,s(T)`: the simple critical-line Xi zeros with ordinate in `(0, T]`. -/
def xiSimpleCriticalZeroCount (T : ℝ) : ℕ :=
  ((stripFinsetPos T).filter
    (fun z => z.re = 1 / 2 ∧ (analyticOrderAt xi z).toNat = 1)).card

/-- `H₁(T)`: the ordinates in `(0, T]` whose complete Xi fiber has total multiplicity one.  Such a
fiber carries exactly one zero, so counting the zeros is the same as counting the ordinates. -/
def xiSingletonFiberCount (T : ℝ) : ℕ :=
  ((stripFinsetPos T).filter (fun z => xiHorizontalMultiplicity z.im = 1)).card

/-! ## The off-line part of one fiber -/

/-- The off-line part of the complete Xi fiber at ordinate `t`. -/
def offLineFiber (t : ℝ) : Finset ℂ :=
  (stripHeightFinset t).filter (fun w => ¬ w.re = 1 / 2)

/-- The critical part of the complete Xi fiber through a critical-line zero is that zero alone:
an ordinate carries at most one point of the critical line. -/
theorem criticalFiber_eq_singleton {z : ℂ} (hz : z ∈ stripHeightFinset z.im)
    (hre : z.re = 1 / 2) :
    (stripHeightFinset z.im).filter (fun w => w.re = 1 / 2) = {z} := by
  ext w
  rw [Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨hw, hwre⟩
    have hwim : w.im = z.im := (mem_stripHeightFinset.mp hw).2.2.1
    exact Complex.ext (by rw [hwre, hre]) hwim
  · rintro rfl
    exact ⟨hz, hre⟩

/-- **Two copies per spoiled ordinate.**  If a simple critical Xi zero does not sit in a singleton
fiber, its ordinate carries at least two off-line copies. -/
theorem two_le_offLineFiber_sum {z : ℂ} (hz : z ∈ stripHeightFinset z.im)
    (hre : z.re = 1 / 2) (hsimple : (analyticOrderAt xi z).toNat = 1)
    (hnot : xiHorizontalMultiplicity z.im ≠ 1) :
    2 ≤ ∑ w ∈ offLineFiber z.im, (analyticOrderAt xi w).toNat := by
  classical
  have hsplit :
      (∑ w ∈ (stripHeightFinset z.im).filter (fun w => w.re = 1 / 2),
          (analyticOrderAt xi w).toNat)
        + ∑ w ∈ offLineFiber z.im, (analyticOrderAt xi w).toNat
        = xiHorizontalMultiplicity z.im := by
    rw [xiHorizontalMultiplicity, offLineFiber]
    exact Finset.sum_filter_add_sum_filter_not _ _ _
  rw [criticalFiber_eq_singleton hz hre, Finset.sum_singleton, hsimple] at hsplit
  have hpos : 0 < ∑ w ∈ offLineFiber z.im, (analyticOrderAt xi w).toNat := by
    rcases Nat.eq_zero_or_pos (∑ w ∈ offLineFiber z.im, (analyticOrderAt xi w).toNat) with h | h
    · exact absurd (by omega) hnot
    · exact h
  obtain ⟨w, hw, hwne⟩ :
      ∃ w ∈ offLineFiber z.im, (analyticOrderAt xi w).toNat ≠ 0 :=
    Finset.exists_ne_zero_of_sum_ne_zero (by omega)
  have hwmem : w ∈ stripHeightFinset z.im := (Finset.mem_filter.mp hw).1
  have hwre : ¬ w.re = 1 / 2 := (Finset.mem_filter.mp hw).2
  have hrefl : lineReflect w ∈ offLineFiber z.im := by
    refine Finset.mem_filter.mpr ⟨lineReflect_mem_stripHeightFinset hwmem, ?_⟩
    rw [lineReflect_re]
    intro h; exact hwre (by linarith)
  have hne : w ≠ lineReflect w := by
    intro h
    apply hwre
    have := congrArg Complex.re h
    rw [lineReflect_re] at this
    linarith
  have hpair : ({w, lineReflect w} : Finset ℂ) ⊆ offLineFiber z.im := by
    intro u hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl
    · exact hw
    · exact hrefl
  have hle := Finset.sum_le_sum_of_subset (f := fun u => (analyticOrderAt xi u).toNat) hpair
  rw [Finset.sum_pair hne, xi_orderAt_lineReflect] at hle
  omega

/-- The off-line part of a fiber through a zero counted by `N(T)` consists of copies counted by
`N(T) − N₀(T)`. -/
theorem offLineFiber_subset {T : ℝ} {z : ℂ} (hz : z ∈ stripFinsetPos T) :
    offLineFiber z.im ⊆ (stripFinsetPos T).filter (fun w => ¬ w.re = 1 / 2) := by
  intro w hw
  rw [offLineFiber, Finset.mem_filter] at hw
  obtain ⟨hwmem, hwre⟩ := hw
  obtain ⟨h1, h2, him, _⟩ := mem_stripHeightFinset.mp hwmem
  obtain ⟨_, _, hzpos, hzle, _⟩ := mem_stripFinsetPos.mp hz
  refine Finset.mem_filter.mpr ⟨mem_stripFinsetPos.mpr ⟨h1, h2, ?_, ?_, ?_⟩, hwre⟩
  · rw [him]; exact hzpos
  · rw [him]; exact hzle
  · exact (mem_stripHeightFinset.mp hwmem).2.2.2

/-! ## The charging inequality -/

/-- **The finite charging law.**  For every height `T`,

```text
2 · N₀,s(T) ≤ 2 · H₁(T) + (N(T) − N₀(T)),
```

equivalently `2 (N₀,s(T) − H₁(T)) ≤ N(T) − N₀(T)`.  Unconditional. -/
theorem two_mul_xiSimpleCriticalZeroCount_le (T : ℝ) :
    2 * xiSimpleCriticalZeroCount T
      ≤ 2 * xiSingletonFiberCount T + xiOffLineZeroCount T := by
  classical
  set A : Finset ℂ :=
    (stripFinsetPos T).filter
      (fun z => z.re = 1 / 2 ∧ (analyticOrderAt xi z).toNat = 1) with hA
  set B : Finset ℂ := A.filter (fun z => ¬ xiHorizontalMultiplicity z.im = 1) with hB
  set C : Finset ℂ := A.filter (fun z => xiHorizontalMultiplicity z.im = 1) with hC
  have hAcard : C.card + B.card = A.card := by
    rw [hB, hC]; exact Finset.card_filter_add_card_filter_not _
  have hCsub : C ⊆ (stripFinsetPos T).filter (fun z => xiHorizontalMultiplicity z.im = 1) := by
    intro z hz
    rw [hC, Finset.mem_filter, hA, Finset.mem_filter] at hz
    exact Finset.mem_filter.mpr ⟨hz.1.1, hz.2⟩
  have hCle : C.card ≤ xiSingletonFiberCount T := Finset.card_le_card hCsub
  -- every element of `B` is a critical-line zero of its own fiber
  have hBmem : ∀ z ∈ B, z ∈ stripFinsetPos T ∧ z.re = 1 / 2 ∧
      (analyticOrderAt xi z).toNat = 1 ∧ xiHorizontalMultiplicity z.im ≠ 1 := by
    intro z hz
    rw [hB, Finset.mem_filter, hA, Finset.mem_filter] at hz
    exact ⟨hz.1.1, hz.1.2.1, hz.1.2.2, hz.2⟩
  have hBfiber : ∀ z ∈ B, z ∈ stripHeightFinset z.im := by
    intro z hz
    obtain ⟨hzmem, _, _, _⟩ := hBmem z hz
    obtain ⟨h1, h2, _, _, hzero⟩ := mem_stripFinsetPos.mp hzmem
    exact mem_stripHeightFinset.mpr ⟨h1, h2, rfl, hzero⟩
  -- distinct spoiled simple critical zeros have distinct ordinates, hence disjoint charges
  have hdisj : (B : Set ℂ).PairwiseDisjoint (fun z => offLineFiber z.im) := by
    intro z hz z' hz' hne
    obtain ⟨_, hzre, _, _⟩ := hBmem z hz
    obtain ⟨_, hz're, _, _⟩ := hBmem z' hz'
    refine Finset.disjoint_left.mpr ?_
    intro w hw hw'
    have h1 : w.im = z.im := (mem_stripHeightFinset.mp (Finset.mem_filter.mp hw).1).2.2.1
    have h2 : w.im = z'.im := (mem_stripHeightFinset.mp (Finset.mem_filter.mp hw').1).2.2.1
    exact hne (Complex.ext (by rw [hzre, hz're]) (by rw [← h1, h2]))
  have hbiUnion : B.biUnion (fun z => offLineFiber z.im)
      ⊆ (stripFinsetPos T).filter (fun w => ¬ w.re = 1 / 2) := by
    intro w hw
    obtain ⟨z, hz, hwz⟩ := Finset.mem_biUnion.mp hw
    exact offLineFiber_subset (hBmem z hz).1 hwz
  have hcharge : 2 * B.card ≤ xiOffLineZeroCount T := by
    have h1 : 2 * B.card = ∑ _z ∈ B, 2 := by
      rw [Finset.sum_const, smul_eq_mul]; ring
    have h2 : ∑ _z ∈ B, 2 ≤ ∑ z ∈ B, ∑ w ∈ offLineFiber z.im, (analyticOrderAt xi w).toNat := by
      refine Finset.sum_le_sum fun z hz => ?_
      obtain ⟨_, hzre, hzsimple, hznot⟩ := hBmem z hz
      exact two_le_offLineFiber_sum (hBfiber z hz) hzre hzsimple hznot
    have h3 : ∑ z ∈ B, ∑ w ∈ offLineFiber z.im, (analyticOrderAt xi w).toNat
        = ∑ w ∈ B.biUnion (fun z => offLineFiber z.im), (analyticOrderAt xi w).toNat :=
      (Finset.sum_biUnion hdisj).symm
    have h4 : ∑ w ∈ B.biUnion (fun z => offLineFiber z.im), (analyticOrderAt xi w).toNat
        ≤ xiOffLineZeroCount T :=
      Finset.sum_le_sum_of_subset hbiUnion
    omega
  have hAeq : A.card = xiSimpleCriticalZeroCount T := rfl
  omega

/-- **The charging law in the card's displayed form.**  Over `ℝ`,

```text
H₁(T) ≥ N₀,s(T) − (N(T) − N₀(T)) / 2.
```
-/
theorem xiSimpleCriticalZeroCount_sub_le_xiSingletonFiberCount (T : ℝ) :
    (xiSimpleCriticalZeroCount T : ℝ) - ((xiPosZeroCount T : ℝ) - (xiPosCriticalZeroCount T : ℝ)) / 2
      ≤ (xiSingletonFiberCount T : ℝ) := by
  have hnat := two_mul_xiSimpleCriticalZeroCount_le T
  have hsplit := xiPosCriticalZeroCount_add_xiOffLineZeroCount T
  have hR : (2 : ℝ) * (xiSimpleCriticalZeroCount T : ℝ)
      ≤ 2 * (xiSingletonFiberCount T : ℝ) + (xiOffLineZeroCount T : ℝ) := by
    exact_mod_cast hnat
  have hRsplit : (xiPosCriticalZeroCount T : ℝ) + (xiOffLineZeroCount T : ℝ)
      = (xiPosZeroCount T : ℝ) := by exact_mod_cast hsplit
  linarith

/-! ## Normalized form and the density passage -/

/-- Every zero counted by `N(T)` has positive Xi order, so any subfamily of ordinates is dominated
by the census. -/
theorem card_le_xiPosZeroCount {T : ℝ} {A : Finset ℂ} (hA : A ⊆ stripFinsetPos T) :
    A.card ≤ xiPosZeroCount T := by
  classical
  calc A.card = ∑ _z ∈ A, 1 := by rw [Finset.sum_const, smul_eq_mul, mul_one]
    _ ≤ ∑ z ∈ A, (analyticOrderAt xi z).toNat := by
        refine Finset.sum_le_sum fun z hz => ?_
        have hzero : xi z = 0 := (mem_stripFinsetPos.mp (hA hz)).2.2.2.2
        exact Nat.one_le_iff_ne_zero.mpr (xi_order_toNat_ne_zero hzero)
    _ ≤ xiPosZeroCount T := Finset.sum_le_sum_of_subset hA

theorem xiSimpleCriticalZeroCount_le (T : ℝ) :
    xiSimpleCriticalZeroCount T ≤ xiPosZeroCount T :=
  card_le_xiPosZeroCount (Finset.filter_subset _ _)

theorem xiSingletonFiberCount_le (T : ℝ) :
    xiSingletonFiberCount T ≤ xiPosZeroCount T :=
  card_le_xiPosZeroCount (Finset.filter_subset _ _)

/-- The critical-line proportion of the census. -/
def xiCriticalRatio (T : ℝ) : ℝ := (xiPosCriticalZeroCount T : ℝ) / (xiPosZeroCount T : ℝ)

/-- The simple-critical-line proportion of the census. -/
def xiSimpleCriticalRatio (T : ℝ) : ℝ := (xiSimpleCriticalZeroCount T : ℝ) / (xiPosZeroCount T : ℝ)

/-- The horizontal-singleton proportion of the census. -/
def xiSingletonFiberRatio (T : ℝ) : ℝ := (xiSingletonFiberCount T : ℝ) / (xiPosZeroCount T : ℝ)

theorem xiCriticalRatio_nonneg (T : ℝ) : 0 ≤ xiCriticalRatio T :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem xiSimpleCriticalRatio_nonneg (T : ℝ) : 0 ≤ xiSimpleCriticalRatio T :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem xiSingletonFiberRatio_nonneg (T : ℝ) : 0 ≤ xiSingletonFiberRatio T :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem xiCriticalRatio_le_one (T : ℝ) : xiCriticalRatio T ≤ 1 := by
  rcases Nat.eq_zero_or_pos (xiPosZeroCount T) with h0 | hpos
  · simp [xiCriticalRatio, h0]
  · rw [xiCriticalRatio, div_le_one (by exact_mod_cast hpos)]
    exact_mod_cast xiPosCriticalZeroCount_le T

theorem xiSimpleCriticalRatio_le_one (T : ℝ) : xiSimpleCriticalRatio T ≤ 1 := by
  rcases Nat.eq_zero_or_pos (xiPosZeroCount T) with h0 | hpos
  · simp [xiSimpleCriticalRatio, h0]
  · rw [xiSimpleCriticalRatio, div_le_one (by exact_mod_cast hpos)]
    exact_mod_cast xiSimpleCriticalZeroCount_le T

theorem xiSingletonFiberRatio_le_one (T : ℝ) : xiSingletonFiberRatio T ≤ 1 := by
  rcases Nat.eq_zero_or_pos (xiPosZeroCount T) with h0 | hpos
  · simp [xiSingletonFiberRatio, h0]
  · rw [xiSingletonFiberRatio, div_le_one (by exact_mod_cast hpos)]
    exact_mod_cast xiSingletonFiberCount_le T

/-- **The normalized charging law.**  For every height,

```text
H₁(T)/N(T) ≥ N₀,s(T)/N(T) − (1 − N₀(T)/N(T))/2,
```

with the degenerate height `N(T) = 0` included (all three ratios are then `0`). -/
theorem xiSimpleCriticalRatio_sub_le_xiSingletonFiberRatio (T : ℝ) :
    xiSimpleCriticalRatio T - (1 - xiCriticalRatio T) / 2 ≤ xiSingletonFiberRatio T := by
  rcases Nat.eq_zero_or_pos (xiPosZeroCount T) with h0 | hpos
  · simp only [xiSimpleCriticalRatio, xiCriticalRatio, xiSingletonFiberRatio, h0, Nat.cast_zero,
      div_zero]
    norm_num
  · have hn : (0 : ℝ) < (xiPosZeroCount T : ℝ) := by exact_mod_cast hpos
    have hnat := two_mul_xiSimpleCriticalZeroCount_le T
    have hsplit : (xiPosCriticalZeroCount T : ℝ) + (xiOffLineZeroCount T : ℝ)
        = (xiPosZeroCount T : ℝ) := by
      exact_mod_cast xiPosCriticalZeroCount_add_xiOffLineZeroCount T
    have hR : (2 : ℝ) * (xiSimpleCriticalZeroCount T : ℝ)
        ≤ 2 * (xiSingletonFiberCount T : ℝ) + (xiOffLineZeroCount T : ℝ) := by
      exact_mod_cast hnat
    have hkey : (2 : ℝ) * (xiSimpleCriticalZeroCount T : ℝ)
        + (xiPosCriticalZeroCount T : ℝ)
        ≤ 2 * (xiSingletonFiberCount T : ℝ) + (xiPosZeroCount T : ℝ) := by linarith
    rw [← sub_nonneg]
    have hrw : xiSingletonFiberRatio T - (xiSimpleCriticalRatio T - (1 - xiCriticalRatio T) / 2)
        = (2 * (xiSingletonFiberCount T : ℝ) + (xiPosZeroCount T : ℝ)
            - (2 * (xiSimpleCriticalZeroCount T : ℝ) + (xiPosCriticalZeroCount T : ℝ)))
          / (2 * (xiPosZeroCount T : ℝ)) := by
      rw [xiSingletonFiberRatio, xiSimpleCriticalRatio, xiCriticalRatio]
      field_simp
      ring
    rw [hrw]
    exact div_nonneg (by linarith) (by linarith)

/-! ### The liminf passage -/

open Filter

/-- **The density passage.**  If the critical-line proportion has lower density at least `κ` and the
simple-critical-line proportion has lower density at least `κs`, then the horizontal-singleton
proportion has lower density at least `κs − (1 − κ)/2`.  This is the card's inequality `(2)`; it is
an unconditional implication between the four actual Xi counting functions. -/
theorem le_liminf_xiSingletonFiberRatio (κ κs : ℝ)
    (hκ : κ ≤ liminf xiCriticalRatio atTop)
    (hκs : κs ≤ liminf xiSimpleCriticalRatio atTop) :
    κs - (1 - κ) / 2 ≤ liminf xiSingletonFiberRatio atTop := by
  have hbddCrit : IsBoundedUnder (fun x y : ℝ => x ≥ y) atTop xiCriticalRatio :=
    isBoundedUnder_of ⟨0, fun T => xiCriticalRatio_nonneg T⟩
  have hbddSimple : IsBoundedUnder (fun x y : ℝ => x ≥ y) atTop xiSimpleCriticalRatio :=
    isBoundedUnder_of ⟨0, fun T => xiSimpleCriticalRatio_nonneg T⟩
  have hcob : IsCoboundedUnder (fun x y : ℝ => x ≥ y) atTop xiSingletonFiberRatio :=
    (isBoundedUnder_of ⟨1, fun T => xiSingletonFiberRatio_le_one T⟩).isCoboundedUnder_ge
  refine le_of_forall_sub_le fun ε hε => ?_
  refine le_liminf_of_le hcob ?_
  have h1 : κ - ε / 2 < liminf xiCriticalRatio atTop := by linarith
  have h2 : κs - ε / 2 < liminf xiSimpleCriticalRatio atTop := by linarith
  have e1 := eventually_lt_of_lt_liminf h1 hbddCrit
  have e2 := eventually_lt_of_lt_liminf h2 hbddSimple
  filter_upwards [e1, e2] with T hT1 hT2
  have hmain := xiSimpleCriticalRatio_sub_le_xiSingletonFiberRatio T
  linarith

/-- **The literature corollary as an exact implication.**  Instantiating the density passage at the
published unconditional proportions `κ ≥ 0.417293962` (critical) and `κs ≥ 0.407511457` (simple
critical) gives lower density `0.116158438` for the horizontal-singleton fibers.  The two inputs
are hypotheses of this statement, so the implication itself is unconditional. -/
theorem prattRoblesZaharescuZeindler_singleton_density
    (hκ : (0.417293962 : ℝ) ≤ liminf xiCriticalRatio atTop)
    (hκs : (0.407511457 : ℝ) ≤ liminf xiSimpleCriticalRatio atTop) :
    (0.116158438 : ℝ) ≤ liminf xiSingletonFiberRatio atTop := by
  have h := le_liminf_xiSingletonFiberRatio 0.417293962 0.407511457 hκ hκs
  norm_num at h
  linarith

end

end RHTower
